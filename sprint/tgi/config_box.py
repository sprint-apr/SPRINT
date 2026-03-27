import os
from dotenv import load_dotenv
from pathlib import Path

load_dotenv()

INFERENCE_MODEL_URL=os.environ.get('INFERENCE_MODEL_URL')
D4J_BUGS_DIR = Path(os.environ.get('D4J_BUGS_DIR'))
D4J_HOME = Path(os.environ.get('D4J_HOME'))

OLLAMA_HOST=os.environ.get('OLLAMA_HOST')

GPT_HOST=os.environ.get('GPT_HOST')
GPT_API_KEY=os.environ.get('GPT_API_KEY')

DATABASE_URL = "postgresql://sprint:sprint@localhost:5432/batch"

PROJECT_ROOT_DIR = Path(__file__).parents[1]

RESOURCES_DIR = Path(__file__).resolve().parent.parent / "resources"
FL4APR_RESOURCES_DIR = PROJECT_ROOT_DIR.parent / 'tool' / "resources"

OPENAI_BATCH_REQUESTS_DIR = RESOURCES_DIR / "batch_requests"
