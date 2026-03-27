import os
from pathlib import Path
from openai import OpenAI

from sprint.tgi import config_box
from sprint.tgi.data import Bug

bugs = None
client = None

API_KEYS = [
    'YOUR_OPENAI_API_KEY_HERE',
]

def get_or_initialize_bugs():
    global bugs
    if not bugs:
        bugs = {
            bug.id: bug for bug in
            [
                Bug.init_from_path(d) for d in config_box.D4J_BUGS_DIR.iterdir()
                if d.is_dir() and not d.name[0].islower()
             ]
        }
    return bugs


def get_or_initialize_client() -> OpenAI:
    global client
    if not client:
        client = OpenAI(api_key=API_KEYS[0])
    return client
