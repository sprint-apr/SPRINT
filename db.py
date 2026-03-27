import json
import click
import requests
from pathlib import Path


from sqlmodel import Session
from sprint.tgi.config_box import D4J_BUGS_DIR, FL4APR_RESOURCES_DIR
from sprint.tgi.db.database import get_session
from sprint.tgi.models import Bug

def initialize_bugs(session: Session):
    # RESOURCES_DIR: set from environment variable or default value
    chatrepair_dir = FL4APR_RESOURCES_DIR / "ChatRepair_patches"
    developer_dir = FL4APR_RESOURCES_DIR / "Developer_patches"
    
    for folder in D4J_BUGS_DIR.iterdir():
        bug_id = folder.name
        project = bug_id.split('_')[0]

        chatrepair_patch, dev_patch = None, None
        if (path := (chatrepair_dir / f'{bug_id}.diff')).exists():
            chatrepair_patch = path.read_text(encoding='utf-8')

        if (path := (developer_dir / f'{bug_id}.diff')).exists():
            dev_patch = path.read_text(encoding='utf-8')
        
        bug = Bug(
            id=bug_id,
            project=project,
            path=str(folder),
            dev_patch=dev_patch,
            chat_repair_patch=chatrepair_patch
        )

        session.add(bug)
        session.commit()

def register_abstract_patches(patches_dir: Path):
    ENDPOINT = "http://localhost:8001/register_abstract_patch"
    for dir in patches_dir.iterdir():
        json_path = dir / 'convert_ir_patches.json'
        abstract_patches = json.loads(json_path.read_text())
        for ap in abstract_patches:
            requests.post(
                url=f'{ENDPOINT}/{patches_dir.name}/{dir.name}',
                json=ap,
            )

def unregister_abstract_patches(version: str):
    ENDPOINT = "http://localhost:8001/abstract_patches"
    requests.delete(url=f'{ENDPOINT}/{version}')


# initialize_bugs(next(get_session()))
register_abstract_patches(Path('/home/june/ap_0309_0642_baseline'))
#unregister_abstract_patches('ap_0309_0642_baseline')
