from typing import Annotated
from fastapi import Depends, Path, HTTPException
from openai import OpenAI
from sqlmodel import Session
from sprint.tgi.db.database import get_session
from sprint.tgi.initializer import get_or_initialize_bugs, get_or_initialize_client
from sprint.tgi.data import Bug

# Dependency for database session
SessionDep = Annotated[Session, Depends(get_session)]


# Dependency for bugs initialization
def get_bugs_dependency():
    """
    Dependency wrapper for get_or_initialize_bugs.
    """
    return get_or_initialize_bugs()


BugsDep = Annotated[dict, Depends(get_bugs_dependency)]


# Dependency for a single bug
def get_bug(bid: str = Path(...), bugs: dict = Depends(get_bugs_dependency)) -> Bug:
    """
    Get the bug object from the bid.
    """
    if bid not in bugs:
        raise HTTPException(status_code=400, detail="Invalid bid")
    return bugs[bid]


BugDep = Annotated[Bug, Depends(get_bug)]


# Dependency for OpenAI client
def get_openai_client():
    """
    Dependency to provide an OpenAI client instance.
    """
    return get_or_initialize_client()

OpenAIClientDep = Annotated[OpenAI, Depends(get_openai_client)]