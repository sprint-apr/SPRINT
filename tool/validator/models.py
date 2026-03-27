from __future__ import annotations
from typing import Optional, List
from enum import Enum as PyEnum
from pydantic import PrivateAttr

from sqlalchemy import Column, Text, UniqueConstraint, Enum as SAEnum
from sqlmodel import Field, SQLModel, Relationship


class AbstractPatch(SQLModel, table=True):
    __tablename__ = "abstractpatch"   
    id: int = Field(primary_key=True)
    bug_id: str = Field(..., description="The bug ID")
    correct: bool | None = Field(nullable=True, default=None)
    file: str = Field(..., description="The source file path")
    line: int = Field(..., description="The line number of the fault")
    procname: str = Field(..., description="The procedure name")
    fault_desc: str = Field(..., description="The fault description")
    sbfl_score: float = Field(..., description="The SBFL score")
    rewriting_instr: str = Field(..., description="The rewriting instruction")
    rewritten_source: Optional[str] = Field(..., description="The rewritten source code")
    matched_part: Optional[str] = Field(..., description="The matched part")
    line_from: int = Field(..., description="The beginning line of the procedure")
    line_to: int = Field(..., description="The ending line of the procedure")
    no_correct: bool | None = Field(nullable=True, default=None)
    pfl : bool | None = Field(description="Whether the patch is from PFL")
    prunned: bool | None = Field(description="Whether the patch is pruned")

    __table_args__ = (
        UniqueConstraint('bug_id', 'file', 'line', 'rewritten_source', name = 'unique_abstract_patch'),
    )


class ExperimentSession(SQLModel, table=True):
    __tablename__ = "experimentsession"
    id: str = Field(primary_key=True)
    model: str = Field(..., description="The model name")


class ConcretePatch(SQLModel, table=True):
    __tablename__  = 'concretepatch'
    id: Optional[int] = Field(default=None, primary_key=True)
    trial: int = Field(description="The trial count")
    abstract_patch_id: int = Field(..., foreign_key="abstractpatch.id", description="The ID of the abstract patch")
    previous_attempt_id: int | None = Field(default=None, foreign_key="concretepatch.id", description="The ID of the previous attempt")
    valid_inference: bool = Field(description="Whether the inference is valid")
    propmt_eval_count: int = Field(..., description="The number of prompt evaluations")
    eval_count: int = Field(..., description="The number of evaluations")
    patch: str = Field(..., description="The concrete patch")
    session_id: str | None = Field(default=None, foreign_key="experimentsession.id", description="The experiment session ID")


class ValidationFlag(PyEnum):
    PASS = "PASS"
    COMPILATION_FAILURE = "COMPILATION_FAILURE"
    TEST_FAILURE = "TEST_FAILURE"
    TIMEOUT = "TIMEOUT"


class Patch(SQLModel, table=True):
    __tablename__ = 'patches'

    id: Optional[int] = Field(default=None, primary_key=True)
    bug_id: str = Field(..., description="The buggy project/bug id")
    source_path: str = Field(..., description="The source file path")
    line_from: int = Field(..., description="Start line")
    line_to: int = Field(..., description="End line")
    # store large patch text using a Text column
    patch_code: str = Field(..., sa_column=Column(Text, nullable=False))
    abstract_patch_id: Optional[int] = Field(default=None, foreign_key="abstractpatch.id")
    concrete_patch_id: Optional[int] = Field(default=None)
    _org_code: str | None = PrivateAttr(default=None)

    __table_args__ = (
        UniqueConstraint('bug_id', 'source_path', 'line_from', 'line_to', 'patch_code', name='unique_patch'),
    )

    # kept: existing utility methods copied as-is
    def create_source(self, project_root, pid):
        import os
        import utils
        basename = os.path.basename(self.source_path)
        base_dir = os.path.join(project_root, 'patches')
        target_dir = os.path.join(base_dir, str(pid))
        utils.make_dir_if_not_exists(base_dir)
        utils.make_dir_if_not_exists(target_dir)
        src = os.path.join(project_root, self.source_path)
        try:
            lines = open(src).read().splitlines(keepends=True)
        except UnicodeDecodeError:
            lines = open(src, encoding='ISO-8859-1').read().splitlines(keepends=True)

        self._org_code = ''.join(lines[self.line_from-1:self.line_to]).replace(r'\r','')
        pre = ''.join(lines[:self.line_from-1])
        post = ''.join(lines[self.line_to:])
        out_path = os.path.join(target_dir, basename)
        with open(out_path, 'w') as f:
            f.write(pre + self.patch_code + '\n' + post)
        with open(src, 'w') as f:
            f.write(pre + self.patch_code + '\n' + post)
        return out_path

    def to_diff(self, project_root, pid):
        import os
        import utils
        buggy = os.path.join(project_root, 'buggy.java')
        fixed = os.path.join(project_root, 'patch.java')
        open(buggy, 'w').write(self._org_code)
        open(fixed, 'w').write(self.patch_code)
        res = utils.execute(f"git diff --no-index {buggy} {fixed}", dir=project_root)
        lines = res.stdout.splitlines()[5:-2]
        diff = '\n'.join(lines) + '\n'
        full = f"{self.source_path}:{self.line_from}~{self.line_to}\n{diff}"
        open(os.path.join(project_root, 'patch.diff'), 'w').write(full)
        return full


class ValidationResult(SQLModel, table=True):
    __tablename__ = 'validation_results'

    id: Optional[int] = Field(default=None, primary_key=True)
    patch_id: int = Field(foreign_key="patches.id")
    flag: ValidationFlag = Field(sa_column=Column(SAEnum(ValidationFlag), nullable=False))
    failed_tests: Optional[int] = Field(default=None)
    compilation_time: Optional[float] = Field(default=None)
    testing_time: Optional[float] = Field(default=None)


class PlausibleResult(SQLModel, table=True):
    __tablename__ = "plausible_results"

    patch_id: int = Field(foreign_key="patches.id", primary_key=True)
    abstract_patch_id: int = Field(foreign_key="abstractpatch.id", primary_key=True)
    session_id: str = Field(nullable=False, primary_key=True)