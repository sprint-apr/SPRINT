import httpx

from sprint.tgi import config_box, prompts
from sprint.tgi.utils import is_valid_inference

async def request(instruction, model):
    if model.startswith('gpt'):
        return await request_gpt(instruction, model)
    else:
        return await request_ollama(instruction, model)

async def request_ollama(instruction, model):
    model_endpoint = f'{config_box.OLLAMA_HOST}/api/chat'

    system_prompt = prompts.PromptBox.instance().get_system_prompts()
    messages = [
        *system_prompt,
        {"role": "user", "content": instruction}
    ]

    async with httpx.AsyncClient() as client:
        try:
            response = await client.post(
                url=model_endpoint,
                timeout=60,
                json={
                    'stream': False,
                    'model': model,
                    'messages': messages,
                })
            response_json = response.json()
            response.raise_for_status()
            model_answer = response_json['message']['content']
            valid_inference = '<patch>' in model_answer and '</patch>' in model_answer
        except (httpx.ReadTimeout, KeyError):
            valid_inference = False,
        finally:
            return {
                **response_json,
                "status_code": response.status_code,
                "valid_inference": valid_inference,
            }

async def request_gpt(instruction, model):
    model_endpoint = f'{config_box.GPT_HOST}/v1/chat/completions'
    headers = {
        'Authorization': f'Bearer {config_box.GPT_API_KEY}',
        'Content-Type': 'application/json',
    }

    system_prompt = prompts.PromptBox.instance().get_system_prompts(version='4o-succeed')
    messages = [
        *system_prompt,
        {"role": "user", "content": instruction}
    ]

    async with httpx.AsyncClient() as client:
        try:
            valid_inference = False
            response = await client.post(
                headers=headers,
                url=model_endpoint,
                timeout=60,
                json={
                    'stream': False,
                    'model': model,
                    'messages': messages,
                })
            response_json = response.json()
            response.raise_for_status()
            model_answer = response_json['choices'][0]['message']['content']
            valid_inference = is_valid_inference(model_answer)
        except (httpx.ReadTimeout, KeyError):
            pass
        finally:
            return {
                **response_json,
                "status_code": response.status_code,
                "valid_inference": valid_inference,
            }