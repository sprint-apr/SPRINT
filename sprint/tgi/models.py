from datetime import datetime, date, timezone
from pydantic import BaseModel, ConfigDict
from sqlalchemy import ARRAY, JSON, UUID, Column, String
from sqlmodel import SQLModel, Field, Relationship
from typing import List, Optional

class SourceLocation(BaseModel):
    file: str = Field(..., description="The source file path")
    line: int = Field(..., description="The line number in the source file")

class Patch(BaseModel):
    id: int = Field(..., description="The patch ID")
    procname: str = Field(..., description="The procedure name")
    location: int = Field(..., description="The location")
    source_location: SourceLocation = Field(..., description="The source location")

class AbstractPatchInput(BaseModel):
    patch_id: int = Field(..., description="The patch ID")
    patch: Patch = Field(..., description="The patch details")
    fault_id: int = Field(..., description="The fault ID")
    fault_desc: str = Field(..., description="The fault description")
    sbfl_score: float = Field(..., description="The SBFL score")
    rewriting_instr: str = Field(..., description="The rewriting instruction")
    rewriting_succeed: bool = Field(..., description="Whether the rewriting succeeded")
    rewritten_source: Optional[str] = Field(..., description="The rewritten source code")
    matched_part: Optional[str] = Field(..., description="The matched part")
    line_range: List[int] = Field(..., description="The line range")

    model_config = ConfigDict(from_attributes=True)

class GeneratePatchesInput(BaseModel):
    abstract_patch_id: int = Field(description="The ID of the abstract patch")
    session_id: str = Field(foreign_key='experimentsession.id', description="The experiment session ID")
    model: str = Field(description="The model to use for generating patches")
    max_trials: int = Field(description="The maximum number of trials for generating the patch")
    previous_attempt_id: int | None = Field(default=None, description="The ID of the previous attempt")

class GeneratePatchesResponse(BaseModel):
    id: int = Field(..., description="The ID of the generated patch")
    

# TODO: Combine pydantic and sqlmodel
from sqlmodel import Field, SQLModel, UniqueConstraint
class AbstractPatch(SQLModel, table=True):
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

# class AbstractPatchVersion(SQLModel, table=True):
#     id: int | None = Field(default=None, primary_key=True)
#     version: str = Field(..., description="Version identifier")
#     last_modified: datetime = Field(default_factory=datetime.now, description="Last modified timestamp")

#     __table_args__ = (
#         UniqueConstraint('version', name='unique_version'),
#     )


# ExperimentSession and ConcretePatch models
class ExperimentSession(SQLModel, table=True):
    id: str = Field(primary_key=True, description="The experiment session ID")
    d4j_version: str | None = Field(default=None, description="The version of the D4J project")
    model: str = Field(..., description="The name of LLM used in the session")
    created_at: datetime = Field(default_factory=datetime.now, description="The creation timestamp")

class ConcretePatch(SQLModel, table=True):
    id: int = Field(default=None, primary_key=True)
    trial: int = Field(description="The trial count")
    abstract_patch_id: int = Field(..., foreign_key="abstractpatch.id", description="The ID of the abstract patch")
    previous_attempt_id: int | None = Field(default=None, foreign_key="concretepatch.id", description="The ID of the previous attempt")
    valid_inference: bool = Field(description="Whether the inference is valid")
    propmt_eval_count: int = Field(..., description="The number of prompt evaluations")
    eval_count: int = Field(..., description="The number of evaluations")
    patch: str = Field(..., description="The concrete patch")
    session_id: str | None = Field(default=None, foreign_key="experimentsession.id", description="The experiment session ID")

class TokenReference(SQLModel, table=True):
    id: int = Field(default=None, primary_key=True)
    abstract_patch_id: int = Field(..., foreign_key="abstractpatch.id", description="The abstract patch this token info belongs to")
    propmt_eval_count: int = Field(..., description="Number of tokens used in prompt")
    eval_count: int = Field(..., description="Number of tokens used in completion")


class UpdateCorrectInput(BaseModel):
    correct: bool | None = Field(..., description="Whether the abstract patch is correct")

class UpdateNoCorrectInput(BaseModel):
    no_correct: bool | None = Field(..., description="Whether the abstract patch is not correct")

class Bug(SQLModel, table=True):
    id: str = Field(primary_key=True, description="The bug ID")
    project: str = Field(..., description="The buggy project name")
    path: str = Field(..., description="The path to the bug dir")
    dev_patch: str | None = Field(default=None, description="The developer's patch")
    chat_repair_patch: str | None = Field(default=None, description="The ChatRepair's patch")

class BatchRequest(SQLModel, table=True):
    id: int = Field(primary_key=True)
    session_id: str = Field(foreign_key="experimentsession.id", description="The ID of the experiment session")
    file_path: str
    batch_index: int
    file_id: str | None = Field(default=None)
    submitted_batch_id: str | None = Field(default=None)
    api_key_used: str | None = Field(default=None, description="The API key used for the batch request")
    submitted_at: datetime | None = Field(default=None)  # recommended addition
    status: str | None = Field(default=None)             # recommended: store status (e.g. 'submitted', 'completed', 'failed')




class BatchRequestItem(SQLModel, table=True):
    custom_id: str = Field(primary_key=True)
    session_id: str = Field(foreign_key="experimentsession.id", description="The ID of the experiment session")
    bug_id: str = Field()
    patch_id: str = Field(..., description="The ID of the patch")
    messages: List[str] = Field(
        sa_column=Column(JSON),
        description="The messages for the batch request"
    )

class APIKeyUsage(SQLModel, table=True):
    __table_args__ = (
        UniqueConstraint("api_key", "model", "date", name="uix_key_model_date"),
    )

    id:       int       = Field(default=None, primary_key=True)
    api_key: str   = Field(nullable=False, index=True)
    model: str = Field(..., description="The model used for the API key")
    date: datetime      = Field(default_factory=lambda: datetime.now(timezone.utc).date(), nullable=False)
    input_tokens:  int  = Field(default=0, nullable=False)
    output_tokens: int  = Field(default=0, nullable=False)
    last_updated: datetime = Field(default_factory=lambda: datetime.now(timezone.utc), nullable=False)

