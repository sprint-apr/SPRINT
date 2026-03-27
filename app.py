import json
import os
from typing import Annotated, List
from fastapi import Depends, FastAPI, HTTPException, Path
from contextlib import asynccontextmanager
from fastapi.middleware.cors import CORSMiddleware

from sqlalchemy import and_, delete, or_
from sqlmodel import Session, select

from sprint.tgi import inference, initializer, prompts
from sprint.tgi.data import AbstractPatch
from sprint.tgi.db.database import create_db_and_tables, get_session
from sprint.tgi.models import (
    AbstractPatchInput,
    AbstractPatch as AbstractPatchDB,
    Bug,
    ConcretePatch,
    GeneratePatchesInput,
    UpdateCorrectInput,
    UpdateNoCorrectInput,
)
from sprint.tgi.routers.batch_router import router as batch_router
from sprint.tgi.routers.session_router import router as session_router

bugs = initializer.get_or_initialize_bugs()


def get_bug(bid: str = Path(...)) -> Bug:
    """
    Get the bug object from the bid.
    """
    if bid not in bugs:
        raise HTTPException(status_code=400, default="Invalid bid")
    return bugs[bid]


SessionDep = Annotated[Session, Depends(get_session)]
BugDep = Annotated[Bug, Depends(get_bug)]


@asynccontextmanager
async def lifespan(app: FastAPI):
    create_db_and_tables()
    yield
    print("finish tgi server")


app = FastAPI(lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_methods=["*"],
    allow_headers=["*"],
)

app.include_router(batch_router)
app.include_router(session_router)


@app.get("/health")
def health():
    return {"status": "ok"}


@app.post("/prompt/{bid}")
async def construct_prompt(request: List[AbstractPatchInput], bug: BugDep):
    abstract_patches = AbstractPatch.from_json(data=request)
    return [
        prompts.construct_from_abstract_patch(bug, patch) for patch in abstract_patches
    ]


@app.post("/generate_patches/{bid}")
async def generate_patches(
    request: GeneratePatchesInput,
    bug: BugDep,
    session: SessionDep,
):
    abstract_patch = session.exec(
        select(AbstractPatchDB).where(AbstractPatchDB.id == request.abstract_patch_id)
    ).first()
    previous_attempt = session.exec(
        select(ConcretePatch).where(ConcretePatch.id == request.previous_attempt_id)
    ).first()
    if previous_attempt and previous_attempt.trial >= request.max_trials:
        raise HTTPException(status_code=400, detail="Max trials exceeded")

    prompt = prompts.construct_from_abstract_patch(
        bug, AbstractPatch.from_db(abstract_patch)
    )
    response = await inference.request(json.dumps(prompt), model=request.model)
    if response.get("status_code", 500) == 200:
        usage = response.get("usage", {})
        concrete_patch = ConcretePatch(
            abstract_patch_id=request.abstract_patch_id,
            trial=previous_attempt.trial + 1 if previous_attempt else 1,
            previous_attempt_id=request.previous_attempt_id,
            valid_inference=response.get("valid_inference", False),
            propmt_eval_count=response.get("prompt_eval_count")
            or usage["prompt_tokens"],
            eval_count=response.get("eval_count") or usage["completion_tokens"],
            patch=response.get("message", {}).get("content", "")
            or response.get("choices", [{}])[0].get("message", {}).get("content", ""),
            session_id=request.session_id,
        )
        session.add(concrete_patch)
        session.commit()
        response["concrete_patch_id"] = concrete_patch.id
        return concrete_patch
    else:
        return response


@app.get("/ask")
async def ask(
    prompt: str,
    abstract_patch_id: int,
    session: SessionDep,
    session_id: str = None,
):
    response = await inference.request_ollama(prompt, model="llama3.1:8b")
    return response


@app.post("/register_abstract_patch/{version}/{bid}")
async def register_abstract_patch(
    version: str, bid: str, request: AbstractPatchInput, session: SessionDep
):
    formers = session.exec(
        select(AbstractPatchDB).where(
            and_(
                AbstractPatchDB.bug_id == bid,
                AbstractPatchDB.file == request.patch.source_location.file,
                AbstractPatchDB.line == request.patch.source_location.line,
                AbstractPatchDB.rewritten_source == request.rewritten_source,
            )
        )
    ).all()

    if not formers:
        input = request.model_dump()
        abstract_patch = {
            k: v
            for k, v in {
                "version": version,
                "bug_id": bid,
                "patch_id": input["patch_id"],
                "file": input["patch"]["source_location"]["file"],
                "line": input["patch"]["source_location"]["line"],
                "procname": input["patch"]["procname"],
                "line_from": input["line_range"][0],
                "line_to": input["line_range"][1],
                **input,
            }.items()
            if k in AbstractPatchDB.__table__.columns.keys()
        }
        session.add(AbstractPatchDB(**abstract_patch))
        session.commit()
        return abstract_patch

    for former in formers:
        former.version = version
    session.commit()
    return formers


@app.delete("/abstract_patches/{version}")
async def delete_abstract_patches(version: str, session: SessionDep):
    query = session.query(AbstractPatchDB).where(AbstractPatchDB.version == version)
    rows = session.exec(query).all()
    query.delete()
    session.commit()
    return {"deleted_rows": len(rows)}


@app.get("/abstract_patches")
async def get_abstract_patches(session: SessionDep):
    return session.exec(select(AbstractPatchDB)).all()


@app.post("/abstract_patches/{id}")
async def check_correct(id: int, update: UpdateCorrectInput, session: SessionDep):
    if (
        abstract_patch := session.exec(
            select(AbstractPatchDB).where(AbstractPatchDB.id == id)
        ).first()
    ) is None:
        raise HTTPException(status_code=404, detail="AbstractPatch not found")
    abstract_patch.correct = update.correct
    session.commit()
    return abstract_patch


@app.post("/abstract_patches/no_correct/{id}")
async def check_no_correct(id: int, update: UpdateNoCorrectInput, session: SessionDep):
    current_row = session.exec(
        select(AbstractPatchDB).where(AbstractPatchDB.id == id)
    ).first()
    related_rows = session.exec(
        select(AbstractPatchDB).where(AbstractPatchDB.bug_id == current_row.bug_id)
    ).all()
    if any(row.correct for row in related_rows):
        raise HTTPException(
            status_code=400,
            detail="Cannot set no_correct if any related rows are correct",
        )

    ret = []
    for row in related_rows:
        row.no_correct = update.no_correct
        row.correct = False
        ret.append(json.loads(row.model_dump_json()))
    session.commit()
    return ret


@app.get("/bugs")
async def get_bugs(session: SessionDep):
    bugs = session.exec(select(Bug)).all()
    return {bug.id: bug for bug in bugs}


@app.get("/prompt")
async def get_prompt(bid: str, version: str, session: SessionDep):
    abstract_patches = session.exec(
        select(AbstractPatchDB).where(
            AbstractPatchDB.bug_id == bid,
            AbstractPatchDB.version == version,
            AbstractPatchDB.rewriting_succeed,
        )
    ).all()
    if not abstract_patches:
        raise HTTPException(status_code=404, detail="AbstractPatches not found")
    return [
        prompts.construct_user_prompt(bugs[bid], AbstractPatch.from_db(patch))
        for patch in abstract_patches
    ]


if __name__ == "__main__":
    import uvicorn

    for key, value in os.environ.items():
        print(key, value)
    uvicorn.run(app, host="0.0.0.0", port=8001)
