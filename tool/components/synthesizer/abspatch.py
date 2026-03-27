import collections
from dataclasses import dataclass
from pathlib import Path
import json
from typing import Optional


@dataclass(frozen=True)
class Key:
    sbfl_score: float
    source_path: str
    faulty_line_loc: int
    faulty_line: str


@dataclass(frozen=True)
class AbsPatch:
    key: Key
    contents: str
    fault_desc: str
    rewriting_succeed: bool
    matched_part: Optional[str]
    rewritten_source: Optional[str]

    def is_insertion(self):
        return self.fault_desc in ["InsertHandle", "SkipStmt", "InsertMethodCall"]

    def is_replacement(self):
        return self.fault_desc in [
            "ExpReplacement",
            "MutateCastingType",
            "MutateVarDeclType",
        ]

    def replace_match(self, old, new, count=1):
        return self.matched_part.replace(old, new, count)

    @classmethod
    def load_abstract_patches(cls, file: Path, root: Path):
        patches = []
        with open(file, "r") as f:
            for p in json.load(f):
                if not p["rewriting_succeed"]:
                    continue
                loc = p["patch"]["source_location"]
                source_path, faulty_line_loc = (loc["file"], loc["line"])
                try:
                    faulty_line = (
                        (root / source_path)
                        .read_text()
                        .split("\n")[faulty_line_loc - 1]
                    )
                except UnicodeDecodeError:
                    faulty_line = (
                        (root / source_path)
                        .read_text("ISO-8859-1")
                        .split("\n")[faulty_line_loc - 1]
                    )
                key = Key(p["sbfl_score"], source_path, faulty_line_loc, faulty_line)
                patches.append(
                    AbsPatch(
                        key,
                        p["patch"]["kind"]["contents"],
                        p["patch"]["kind"]["name"][0],
                        p["rewriting_succeed"],
                        p["matched_part"],
                        p["rewritten_source"].strip(),
                    )
                )
        return patches

    @classmethod
    def sort_and_group_by_line(cls, patches):
        d = collections.defaultdict(list)
        for p in patches:
            d[p.key].append(p)

        return dict(
            sorted(d.items(), key=lambda item: item[0].sbfl_score, reverse=True)
        )
