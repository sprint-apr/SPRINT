from fastapi import APIRouter, HTTPException
from sqlmodel import select
from sprint.tgi.models import ExperimentSession
from sprint.tgi.dependencies import SessionDep

router = APIRouter(prefix="/session", tags=["session"])


@router.post("/create")
async def create_session(id: str, ap_version: str, model: str, session: SessionDep):
    """
    Create a new experiment session.
    """
    # Check if the session already exists
    existing_session = session.exec(
        select(ExperimentSession).where(ExperimentSession.id == id)
    ).first()

    if existing_session:
        raise HTTPException(
            status_code=400, detail="Session with this ID already exists."
        )

    # Create a new session
    new_session = ExperimentSession(id=id, ap_version=ap_version, model=model)
    session.add(new_session)
    session.commit()

    return {"id": new_session.id}
