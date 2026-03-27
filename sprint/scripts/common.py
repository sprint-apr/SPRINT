from sqlalchemy import select
from sprint.tgi.db.database import get_session
from sprint.tgi.models import ExperimentSession


def ensure_session_exists(session_id: str):
    """
    Ensure that the given session_id exists. If not, create it.
    """
    with next(get_session()) as session:
        existing_session = session.exec(select(ExperimentSession).where(ExperimentSession.id == session_id)).first()
        if not existing_session:
            new_session = ExperimentSession(id=session_id)
            session.add(new_session)
            session.commit()
