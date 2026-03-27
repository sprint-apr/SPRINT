import utils
from enum import Enum, auto
from pathlib import Path
from typing import List, Optional
import dataclasses
from dataclasses import dataclass


class PruningFlag(Enum):
    SAT = ['SAT']
    UNSAT = ['UNSAT']
    OOS = ['OutOfScope']
    REDUNDANT = ['Redundant']


class ValidationFlag(Enum):
    PLAUSIBLE_FOUND = auto()
    COMPILATION_FAILURE = auto()
    FAILING_TEST_NOT_PASSED = auto()
    REGRESSION_FAILED = auto()
    TIMEOUT = auto()


@dataclass
class Patch:
    @dataclass
    class RewritingResult:
        cmd: str
        succeed: bool
        source_path: Optional[str] = None
        patch_class_path: Optional[str] = None

        def __init__(self, d):
            self.cmd = d['cmd']
            self.succeed = d['succeed']
            if self.succeed:
                self.source_path = str(d['res'])
                self.patch_class_path = '/'.join(
                    self.source_path.split(sep='/')[:2])

    @dataclass
    class ValidationResult:
        elapsed_time: int
        flag: ValidationFlag = None
        compilation_time: int = 0.0
        failing_test_time: int = 0.0
        regression_test_time: int = 0.0

    id: int
    template: str
    contents: str
    procname: str
    node_id: int
    original_source_path: str
    source_line: int

    pruning_result: Optional[PruningFlag] = None
    rewriting_result: Optional[RewritingResult] = None
    validation_result: Optional[ValidationResult] = None

    def __init__(self, d):
        self.id = d['patch_id']
        p = d['patch']
        self.template = p['kind']['name'][0]
        self.contents = p['kind']['name'][0]
        self.procname = p['procname']
        self.node_id = p['location']
        self.original_source_path = p['source_location']['file']
        self.source_line = p['source_location']['line']

        if ((r := d['pruning_result'])) is not None:
            self.pruning_result = PruningFlag(r)
        if ((r := d['rewriting_result'])) is not None:
            self.rewriting_result = Patch.RewritingResult(r)

    def is_converted(self):
        return self.rewriting_result != None and self.rewriting_result.succeed

    def get_patch_source_path(self):
        return self.rewriting_result.source_path

    def get_patch_class_path(self):
        return self.rewriting_result.patch_class_path

    def asdict(self):
        return dataclasses.asdict(self, dict_factory=lambda data:
                                  dict((k, v.name if isinstance(v, Enum) else v) for k, v in data))


def from_ocaml_result_json(result_path: Path) -> List[Patch]:
    try:
        return [Patch(d) for d in utils.read_json_from_file(result_path)]
    except Exception as e:
        print(e)
        return []
