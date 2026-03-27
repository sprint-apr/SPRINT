import tiktoken
import toml
import re

from sprint.tgi.data import AbstractPatch, Bug
from sprint.tgi.config_box import D4J_HOME, RESOURCES_DIR

class PromptBox:
  __instance = None

  def __init__(self, system_prompts):
    self.system_prompts = {}
    for version in system_prompts['version']:
      self.system_prompts[version['id']] = version['prompts']

  @classmethod
  def instance(cls):
    if cls.__instance:
      return cls.__instance

    with open(RESOURCES_DIR / "prompt.toml", 'r') as f:
      system_prompts = toml.load(f)

    cls.__instance = cls(system_prompts)
    return cls.__instance

  def get_system_prompts(self, version="gpt4o"):
    return self.system_prompts[version]


def construct_bug_info(bug: Bug):
  bug_index = bug.id.split('_')[-1]
  D4J_META_DIR = D4J_HOME / 'framework' / 'projects' / bug.project_name 
  patch_file = (D4J_META_DIR / 'patches' / bug_index).with_suffix('.src.patch')
  modified_files = re.findall( r'^diff --git a/(.+?) b/', patch_file.read_text(), re.MULTILINE)
  source_files = [bug.root / path for path in modified_files]

  trigger_test_log = D4J_META_DIR / 'trigger_tests' / bug_index 
  return {
    'source_files': [str(path.relative_to(bug.root)) + "\n" + path.read_text() for path in source_files],
    'test_log': trigger_test_log.read_text()
  }

def construct_from_abstract_patch(bug: Bug, patch: AbstractPatch):
  source_file = bug.root / patch.source_path
  [line_start, line_end] = patch.line_range

  lines = source_file.read_text().splitlines()
  patched_line_content = patch.rewritten_source + (
    "\n" + lines[patch.modified_line - 1] if patch.is_insertion else ""
  )
  lines[patch.modified_line - 1] = patched_line_content
  modified_method_lines = lines[(line_start - 1):line_end]  

  bug_index = bug.id.split('_')[-1]
  D4J_META_DIR = D4J_HOME / 'framework' / 'projects' / bug.project_name 
  trigger_test_log = D4J_META_DIR / 'trigger_tests' / bug_index
  return {
    'source_lines': modified_method_lines,
    'test_log': trigger_test_log.read_text(),
  }

def construct_user_prompt(bug: Bug, patch: AbstractPatch):
    source_file = bug.root / patch.source_path
    [line_start, line_end] = patch.line_range

    lines = source_file.read_text(errors="ignore").splitlines()
    patched_line_content = patch.rewritten_source.replace('"<MASK>"', '<MASK>') + (
        "\n" + lines[patch.modified_line - 1] if patch.is_insertion else ""
    )
    lines[patch.modified_line - 1] = patched_line_content
    modified_method_lines = lines[(line_start - 1):line_end]

    is_insertion = patch.is_insertion \
        or (patch.rewritten_source.startswith('"<MASK>"\n') and patch.rewritten_source != "<MASK>")

    instruction = (
        "Generate 10 patches.\n"
    )

    masked_code_section = (
        f"#### masked_code:\n"
        f"```java\n"
        f"{'\n'.join(modified_method_lines)}\n"
        f"```\n\n"
    )

    original_code_section = (
        f"#### original_code:\n"
        f"```java\n"
        f"{patch.matched_part}\n"
        f"```\n\n"
    ) if not is_insertion else ""

    err_logs = (
        f"#### err_logs:\n"
        f"```\n"
        f"{bug.err_logs}\n"
        f"```\n\n"
    )

    return f"{instruction}{masked_code_section}{original_code_section}{err_logs}"

def construct_openai_messages(bug: Bug, patch: AbstractPatch):
  system_prompt = PromptBox.instance().get_system_prompts(version="gpt4o-simple-0601")
  user_prompt = construct_user_prompt(bug, patch)
  return [
      *system_prompt,
      {"role": "user", "content": user_prompt}
  ]


def truncate_matched_part_by_tokens(patch: AbstractPatch, model="gpt-4.1-mini", max_tokens=1250):
    '''
    THIS FUNCTION IS NOT USED. WE DO NOT TRUNCATE MATCHED PART ANYMORE. 
    '''
    encoding = tiktoken.encoding_for_model(model)

    lines = patch.matched_part.splitlines()
    modified_idx = patch.modified_line - patch.line_range[0]  # relative line number

    tokenized_lines = [(i, line, encoding.encode(line)) for i, line in enumerate(lines)]
    total_lines = len(tokenized_lines)

    window = []
    token_count = 0

    left = modified_idx
    right = modified_idx + 1

    if 0 <= modified_idx < total_lines:
        line = tokenized_lines[modified_idx]
        window.append(line)
        token_count += len(line[2])

    while token_count < max_tokens and (left > 0 or right < total_lines):
        if left > 0:
            left -= 1
            line = tokenized_lines[left]
            if token_count + len(line[2]) <= max_tokens:
                window.insert(0, line)
                token_count += len(line[2])
        if right < total_lines:
            line = tokenized_lines[right]
            if token_count + len(line[2]) <= max_tokens:
                window.append(line)
                token_count += len(line[2])
            right += 1

    truncated_text = "\n".join(line[1] for line in window)
    return truncated_text
 