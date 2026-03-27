import os

from openai import OpenAI

D4J_V12_PROJECTS = [
    "Chart",
    "Closure",
    "Lang",
    "Math",
    "Mockito",
    "Time",
]

def upload_openai_files(files: list[str], openai_client: OpenAI) -> list[str]:
    """
    Upload files to OpenAI and return their IDs.
    """
    assert all(os.path.exists(file) for file in files)

    file_ids = []
    for file_path in files:
        with open(file_path, 'rb') as f:
            response = openai_client.files.create(file=f, purpose='batch')
            file_ids.append(response.id)
    
    return file_ids

def is_valid_inference(model_answer: str) -> bool:
    """
    Check if the model answer contains valid inference markers.
    """
    return '<patch_code>' in model_answer and '</patch_code>' in model_answer

def is_d4j_v12(bug_id: str) -> bool:
    """
    Check if the bug ID corresponds to a D4J v1.2 bug.
    """
    return any(bug_id.startswith(proj) for proj in D4J_V12_PROJECTS)


TOKEN_REFERENCE_SESSION = ["0617-nano-perbug", "0616-nano-reference-5", "0616-nano-reference-3", "0616-nano-reference", "0608-nano-reference"]
AVERAGE_INPUT_TOKENS = 1065
AVERAGE_OUTPUT_TOKENS = 760