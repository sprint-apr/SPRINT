import os
import json
from dataclasses import dataclass
from .template import Template, Insertion
import pandas as pd


@dataclass
class Patch:
    source_path: str
    bug_id: str
    line_from: int
    line_to: int
    patch_code: str
    sbfl_score: float
    inference_score: float

    def key(self):
        patch_code = "".join(self.patch_code.split())
        return f"{self.bug_id}@,{self.source_path}@,{self.line_from},{self.line_to}@,{patch_code}"

    def create_source(self, project_root_dir, patch_id):
        basename = os.path.basename(self.source_path)
        dirname = f"{project_root_dir}/patches/{patch_id}"
        os.makedirs(dirname, exist_ok=True)

        with open(f"{project_root_dir}/{self.source_path}", "r") as org_file:
            lines = org_file.readlines()
            pre_line = "".join(lines[: self.line_from - 1])
            post_line = "".join(lines[self.line_to :])

        with open(f"{dirname}/{basename}", "w") as patch_file:
            patch_file.write(pre_line + self.patch_code + "\n" + post_line)

        return f"{dirname}/{basename}"


@dataclass
class Row:
    ID: str
    source_path: str
    SBFL_score: float
    lineno: int
    faulty_line: str
    width: int
    template: str
    masked_line: str
    is_insertion: bool
    elapsed_time: float | None = None
    beam_time: float | None = None
    change: str | None = None
    dedup: str | None = None
    value: float | None = None

    @classmethod
    def create(cls, id, configuration, template: Template):
        return cls(
            id,
            template.source_path,
            template.sbfl_score,
            template.faulty_line_loc,
            template.faulty_line,
            configuration.beam_width,
            template.__class__.__name__,
            template.masked_line,
            isinstance(template, Insertion),
        )

    def values(self):
        return [
            value for field, value in self.__dict__.items() if not field.startswith("_")
        ]

    def update_beam_generation(self, elapsed_time, beam_time, change, value):
        self.elapsed_time = elapsed_time
        self.beam_time = beam_time
        self.change = change
        # this dedup logic is from AlphaReapir
        if self.change != None:
            self.dedup = (
                change.replace(" ", "")
                .replace("#", "")
                .replace("\n", "")
                .replace("\t", "")
            )
        self.value = value


class DataFrame(pd.DataFrame):
    def __init__(self, project_id, configuration):
        super().__init__(columns=Row.__annotations__.keys())
        self.project_id = project_id
        self.configuration = configuration
        self.verbose = configuration.verbose

    @classmethod
    def initialize(cls, project_id, configuration):
        return cls(project_id, configuration)

    def update_row(
        self,
        template,
        elapsed_time=None,
        beam_time=None,
        change=None,
        proba=None,
    ):
        row = Row.create(self.project_id, self.configuration, template)
        row.update_beam_generation(elapsed_time, beam_time, change, proba)
        self.loc[len(self)] = row.values()
        if self.verbose and len(self) % 100 == 0:
            print(self)

    def store_patches_into_json(self, json_file):
        patches = []
        for index, row in self.iterrows():
            d = row.to_dict()
            if d["is_insertion"]:
                patch_code = d["change"] + "\n" + d["faulty_line"]
            else:
                patch_code = d["change"]

            patches.append(
                Patch(
                    d["source_path"],
                    d["ID"],
                    d["lineno"],
                    d["lineno"],
                    patch_code,
                    d["SBFL_score"],
                    d["value"],
                ).__dict__
            )
        with open(json_file, "w") as f:
            json.dump(patches, f, indent=4)

    def dedup_and_sort(self):
        self.sort_values(by=["SBFL_score", "value"], ascending=False, inplace=True)
        self.drop_duplicates(
            subset=["source_path", "lineno", "dedup"], inplace=True, ignore_index=True
        )
