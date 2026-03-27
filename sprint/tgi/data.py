from dataclasses import dataclass
from pathlib import Path
import re
from typing import List, Union

from sprint.tgi.config_box import D4J_HOME
from sprint.tgi.models import AbstractPatchInput, AbstractPatch as AbstractPatchDB

@dataclass
class Bug:
    id: str
    project_name: str
    root: Path

    @classmethod
    def init_from_path(cls, project_root_dir: Path):
        name = project_root_dir.name
        return cls(
            id=name,
            project_name=name.split('_')[0],
            root=project_root_dir,
        )


    @property
    def err_logs(self):
        D4J_META_DIR = D4J_HOME / 'framework' / 'projects' / self.project_name 
        trigger_test_log = D4J_META_DIR / 'trigger_tests' / (self.id.split('_')[-1])
        pattern = r"---.*?(?=\t+at)"
        matches = re.findall(pattern, trigger_test_log.read_text(), re.DOTALL)
        return "\n".join([match.strip() + "\n" for match in matches])


@dataclass
class AbstractPatch:
    id: str
    source_path: Path
    modified_line: int
    line_range: List[int]
    rewritten_source: str
    is_insertion: bool
    matched_part: str

    @classmethod
    def from_db(cls, data: AbstractPatchDB):
        return cls(
            id=data.id,
            source_path=Path(data.file),
            modified_line=data.line,
            line_range=[data.line_from, data.line_to],
            rewritten_source=data.rewritten_source,
            is_insertion=(data.fault_desc in ['MissingErrorHandling', 'MissingSideEffect']),
            matched_part=data.matched_part
        )

    @classmethod
    def from_json(cls, data: List[AbstractPatchInput]):
        patches = []
        for d in data:
            if not d.rewriting_succeed:
                continue
            patches.append(cls.__from_single_input(d))

        return patches

    @classmethod
    def __from_single_input(cls, d: AbstractPatchInput):
        srcloc = d.patch.source_location
        return cls(
            id=d.patch_id,
            source_path=Path(srcloc.file),
            modified_line=srcloc.line,
            line_range=d.line_range,
            rewritten_source=d.rewritten_source,
            is_insertion=(d.fault_desc == 'MissingErrorHandling'),
        )
