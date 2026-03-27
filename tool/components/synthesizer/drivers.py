import re
import typing
import abc
import time
import pprint
import os
import traceback
import torch
import sqlite3
from tqdm import tqdm
from dataclasses import dataclass, field
from collections import namedtuple
from pathlib import Path
from . import llm
from .status import DataFrame
from .template import Template, Insertion
from .abspatch import AbsPatch, Key
from .alpha_repair import templates as alpha_repair_templates
from .bert_only import templates as bert_only_templates


def comment_remover(text):
    def replacer(match):
        s = match.group(0)
        if s.startswith("/"):
            return " "  # note: a space and not an empty string
        else:
            return s

    pattern = re.compile(
        r'//.*?$|/\*.*?\*/|\'(?:\\.|[^\\\'])*\'|"(?:\\.|[^\\"])*"',
        re.DOTALL | re.MULTILINE,
    )
    return re.sub(pattern, replacer, text)


class Project:
    ochiai_file_name = "ochiai.txt"
    source_dir_rel_paths = {
        "Chart": ["source"],
        "Closure": ["src"],
        "Lang": ["src/java", "src/main/java"],
        "Math": ["src/main/java", "src/java"],
        "Mockito": ["src"],
        "Time": ["src/main/java"],
        "Cli": ["src/java", "src/main/java"],
        "Codec": ["src/java", "src/main/java"],
        "Collections": ["src/main/java"],
        "Compress": ["src/main/java"],
        "Csv": ["src/main/java"],
        "Gson": ["gson/src/main/java"],
        "JacksonCore": ["src/main/java"],
        "JacksonDatabind": ["src/main/java"],
        "JacksonXml": ["src/main/java"],
        "Jsoup": ["src/main/java"],
        "JxPath": ["src/java"],
    }

    def __init__(self, project_root_dir, configuration):
        self.root = Path(os.path.abspath(project_root_dir))
        self.id = os.path.basename(self.root)
        self.project_name = self.id.split("_")[0]
        self.patches_json_file_path = (
            configuration.patches_dir / self.id / "patches.json"
        )
        self.ochiai_file_path = self.root / self.ochiai_file_name
        print(self.id)
        print(self.source_dir_rel_paths[self.project_name])
        if not (
            source_dir := self.root / self.source_dir_rel_paths[self.project_name][0]
        ).exists():
            source_dir = self.root / self.source_dir_rel_paths[self.project_name][1]
        self.source_dir = source_dir


@dataclass
class Configuration:
    trial_id: str
    beam_width: int
    generate_beam: bool
    abspatch_dir: Path
    abspatch_limit: int
    num_max_patches: int
    timeout: int
    device: str | None = None
    verbose: bool = False

    abstract_patch_json_name = "convert_ir_patches.json"

    def __post_init__(self):
        self.patches_dir = Path(self.trial_id).with_suffix(".patches")
        os.makedirs(self.patches_dir, exist_ok=True)

    def to_json(self):
        import json

        d = self.__dict__.copy()
        d["abspatch_dir"] = str(d["abspatch_dir"])
        d["patches_dir"] = str(d["patches_dir"])
        return json.dumps(d, indent=4)


@dataclass
class Probe:
    status: str = "INIT"
    exception_traceback: str | None = None
    num_abstract_patches: int = 0
    num_templates: int = 0
    num_generated_patches: int = 0
    empty_patches: bool = False
    beam_gen_failed: bool = False
    beam_gen_failures: list[str] = field(default_factory=list)

    def __post_init__(self):
        self.time_begin = time.time()

    def write(self, dir: Path, trial_id: str):
        import json

        with open(dir / (trial_id + ".probe"), "w") as f:
            json.dump(self.__dict__, f, indent=4)


class Driver(abc.ABC):
    PrePostKey = namedtuple(
        "PrePostKey", ["source_path", "faulty_line_loc", "is_insertion"]
    )

    def __init__(
        self,
        model: llm.Model,
        conf: Configuration,
        conn: sqlite3.Connection,
    ):
        self.model = model
        self.tokenizer = model.tokenizer
        self.token_size_counter = model.token_size_counter
        self.max_token_size = model.max_token_size
        self.infill_token = model.infill_token
        self.conf = conf
        self.conn = conn
        self.input_cache: dict[self.PrePostKey, tuple[str, str]] = dict()

    @abc.abstractmethod
    def enumerate_templates(self, abspatches, limit=None):
        pass

    @abc.abstractmethod
    def load_abstract_patches(self, project: Project, limit=None):
        pass

    def compute_pre_post_inputs(self, root: Path, template: Template):
        key = self.PrePostKey(
            source_path=template.source_path,
            faulty_line_loc=template.faulty_line_loc,
            is_insertion=isinstance(template, Insertion),
        )

        if key not in self.input_cache:
            self.input_cache[key] = self.preprocess(
                root / key.source_path,
                key.faulty_line_loc,
                not key.is_insertion,
            )
        return self.input_cache[key]

    def run(self, project: Project):
        probe = Probe()
        df = DataFrame.initialize(project.id, self.conf)

        if (abspatches := self.load_abstract_patches(project)) == []:
            probe.status = "NO_ABSTRACT_PATCHES"
            print(msg := f"{project.id}, {probe.status}")
            return msg, probe
        else:
            os.makedirs(self.conf.patches_dir / project.id, exist_ok=True)

        cursor = self.conn.cursor()
        cursor.execute(
            f"""
            CREATE TABLE IF NOT EXISTS {project.id}_results (
                id INT AUTO_INCREMENT PRIMARY KEY,
                source_path TEXT,
                faulty_line_loc INT,
                is_insertion TEXT,
                masked_line TEXT,
                beam_size INT,
                beam_results TEXT,
                beam_time DECIMAL(10, 2)
            )
            """
        )
        self.conn.commit()

        try:
            # load abstract patches
            probe.status = "ABSPATCH_ENUMERATED"
            probe.num_abstract_patches = len(abspatches)
            with torch.no_grad():
                self.__run(
                    project,
                    df,
                    probe,
                    abspatches,
                    limit=self.conf.abspatch_limit,
                )
        except Exception:
            probe.status = "EXCEPTION_OCCURS"
            probe.exception_traceback = traceback.format_exc().split("\n")
        finally:
            if probe.num_generated_patches == 0:
                probe.empty_patches = True
            if self.conf.generate_beam:
                df.dedup_and_sort()
            df.to_csv(project.root / (self.conf.trial_id + ".csv"))
            df.store_patches_into_json(project.root / (self.conf.trial_id + ".json"))
            df.store_patches_into_json(project.patches_json_file_path)
            probe.write(project.root, self.conf.trial_id)
        print(
            msg := f"{project.id}, {probe.status}, {probe.beam_gen_failed}, {time.time() - probe.time_begin}"
        )
        return msg, probe

    def __run(self, project, df, probe, abspatches, limit=None):
        # enumerate masked templates
        templates = self.enumerate_templates(abspatches, limit)
        probe.status = "TEMPLATES_ENUMERATED"
        probe.num_templates = len(templates)

        if not self.conf.generate_beam:
            for template in templates:
                df.update_row(template)
            return df

        elapsed_time = time.time() - probe.time_begin

        # do beam searches
        current_line = None
        for template in tqdm(templates) if self.conf.verbose else templates:
            # check if line has been changed, and if so, drop duplicated patches
            if current_line != template.faulty_line_loc and self.conf.generate_beam:
                # update the current line
                current_line = template.faulty_line_loc
                df.dedup_and_sort()
                probe.num_generated_patches = len(df)

                # enough patches are generated, so skip the remaining searches
                if probe.num_generated_patches >= self.conf.num_max_patches:
                    probe.status = "TOO_MANY_PATCHES"
                    return df

            # times up, skip the remaining searches
            if elapsed_time > self.conf.timeout:
                probe.status = "TIMEOUT"
                return df

            time_begin_pp = time.time()
            pre_code_input, post_code_input = self.compute_pre_post_inputs(
                project.root, template
            )
            elapsed_time += time.time() - time_begin_pp

            try:
                beam_generation_result = self.model.generate_beam(
                    template, pre_code_input, post_code_input, project.id, self.conn
                )

                # inference fails, may be input token length exceeds model's limit
                if beam_generation_result is None:
                    continue

                beam_results, beam_time = beam_generation_result

                elapsed_time += beam_time

            except Exception:
                traceback.print_exc()
                probe.beam_gen_failed = True
                probe.beam_gen_failures.append(
                    template.masked_line + "\n" + str(template)
                )

            for change, proba in beam_results:
                df.update_row(
                    template,
                    elapsed_time,
                    beam_time,
                    change,
                    proba,
                )

        probe.status = "PATCHES_GENERATED"

        return df

    def preprocess(self, source_path, line_loc, inplace):
        try:
            with open(source_path, "r", encoding="utf-8", errors="ignore") as f:
                data = f.readlines()
        except UnicodeDecodeError:
            with open(source_path, "r", encoding="ISO-8859", errors="ignore") as f:
                data = f.readlines()

        if inplace:
            pre_code, middle_code, post_code = (
                data[: line_loc - 1],
                data[line_loc - 1],
                data[line_loc:],
            )
        else:
            pre_code, middle_code, post_code = (
                data[: line_loc - 1],
                data[line_loc - 1],
                data[line_loc:],
            )

        line_size = 100

        """
            InsertThrow in BertOnly model may exceed the token limit with the preprocessing logic,
            so we set a tighter restriction (480)
        """
        max_token_size = self.max_token_size - (22 if inplace else 32)
        while 1:
            pre_code_input = "</s> " + " ".join(
                [x.strip() for x in pre_code[-line_size:]]
            )
            post_code_input = (
                " ".join([x.strip() for x in post_code[0:line_size]])
                .replace("\n", "")
                .strip()
            )
            if (
                self.token_size_counter(pre_code_input + middle_code + post_code_input)
                < max_token_size
            ):
                break
            line_size -= 1

        return pre_code_input, post_code_input


class AlphaRepair(Driver):
    def __init__(self, conf, conn):
        super().__init__(
            llm.CodeBert(conf),
            conf,
            conn,
        )

    def load_abstract_patches(self, project: Project, limit=None):
        lines = project.ochiai_file_path.read_text().strip().split("\n")
        dummies = []

        for line in lines:
            chunks = line.split("#")
            qualified_classname = chunks[0]
            faulty_line_loc = int(chunks[1].split(",")[0])
            sbfl_score = float(chunks[1].split(",")[1])
            source_path = (
                project.source_dir / qualified_classname.replace(".", "/")
            ).with_suffix(".java")

            # skip test codes
            if not source_path.exists():
                continue

            try:
                source_text = source_path.read_text(encoding="utf-8", errors="ignore")
            except UnicodeDecodeError:
                source_text = source_path.read_text(
                    encoding="ISO-8859", errors="ignore"
                )

            if faulty_line_loc >= len(source_text.split("\n")):
                continue

            key = Key(
                sbfl_score=sbfl_score,
                source_path=str(source_path),
                faulty_line_loc=faulty_line_loc,
                faulty_line=source_text.split("\n")[faulty_line_loc - 1],
            )
            dummies.append(
                AbsPatch(key, "", "ExpReplacement", True, None, None),
            )

        """
        for line in lines:
            sbfl_score = float(line.split(";")[-1].strip())
            qualified_classname = line.split("#")[0].replace("$", ".")
            source_path = (
                project.source_dir / qualified_classname.replace(".", "/")
            ).with_suffix(".java")

            # skip test codes
            if not source_path.exists():
                continue

            faulty_line_loc = int(line.split(":")[-1].split(";")[0])
            try:
                source_text = source_path.read_text(encoding="utf-8", errors="ignore")
            except UnicodeDecodeError:
                source_text = source_path.read_text(
                    encoding="ISO-8859", errors="ignore"
                )
            key = Key(
                sbfl_score=sbfl_score,
                source_path=str(source_path),
                faulty_line_loc=faulty_line_loc,
                faulty_line=source_text.split("\n")[faulty_line_loc - 1],
            )
            dummies.append(
                AbsPatch(key, "", "ExpReplacement", True, None, None),
            )
        """
        return dummies

    def enumerate_templates(self, abspatches, limit=None | int):
        ret = []

        for idx, (key, grp) in enumerate(
            AbsPatch.sort_and_group_by_line(abspatches).items()
        ):
            template_classes = [
                alpha_repair_templates.LineReplacement,
                alpha_repair_templates.PartialTemplate,
                alpha_repair_templates.MatchTemplate,
                alpha_repair_templates.SimpleOperator,
            ]

            for template in template_classes:
                ret.extend(
                    template.enumerate(
                        key.source_path,
                        key.faulty_line_loc,
                        key.faulty_line,
                        key.sbfl_score,
                        self.tokenizer,
                    )
                )
        return ret


class BertOnly(Driver):
    def __init__(self, conf, conn):
        super().__init__(
            llm.CodeBert(conf),
            conf,
            conn,
        )

        self.replacement_templates = [
            bert_only_templates.SimpleReplacement,
            bert_only_templates.MutateCondition,
            bert_only_templates.MutateOperator,
            bert_only_templates.MatchTemplate,
        ]

    def load_abstract_patches(self, project: Project, limit=None):
        if not (
            abspatch_json := self.conf.abspatch_dir
            / project.id
            / self.conf.abstract_patch_json_name
        ).exists():
            return []

            # load abstract patches
        return AbsPatch.load_abstract_patches(abspatch_json, project.root)

    def enumerate_templates(self, abspatches, limit=None | int):
        ret = []
        for idx, p in enumerate(abspatches):
            if p.fault_desc == "ExpReplacement":
                for template in self.replacement_templates:
                    ret.extend(template.enumerate(p))
            elif p.fault_desc == "MutateCastingType":
                ret.extend(bert_only_templates.MutateCastingType.enumerate(p))
            elif p.fault_desc == "MutateVarDeclType":
                ret.extend(bert_only_templates.MutateVarDeclType.enumerate(p))
            elif p.fault_desc == "InsertHandle":
                ret.extend(bert_only_templates.InsertHandle.enumerate(p))
            else:
                ret.extend(bert_only_templates.SkipStmt.enumerate(p))
        return ret
