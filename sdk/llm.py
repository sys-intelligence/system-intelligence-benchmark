"""LLM class using LiteLLM for unified API access."""

import pprint
import sys
import time

from litellm import completion

from sdk.logger import logger


class LLM:
    """LLM class for model API."""

    def __init__(
        self,
        engine,
        system_prompt: str = 'You are an AI assistant that helps people find information.',
        temperature: float = 0.1,
        past_message_num: int = sys.maxsize,
        json_format: bool = False,
    ) -> None:
        """Initialize the LLM class."""
        self.name = engine
        self.system_prompt = system_prompt
        self.past_message_num = max(0, past_message_num)
        self.messages = [
            {
                'role': 'system',
                'content': self.system_prompt,
            }
        ]
        self.parameters = {
            'model': engine,
            'temperature': temperature,
            'max_tokens': 2000,
            'top_p': 0.95,
            'frequency_penalty': 0,
            'presence_penalty': 0,
            'stop': None,
        }
        if engine == 'o4-mini':
            self.parameters = {
                'model': engine,
                'temperature': 1,
                'max_completion_tokens': 2000,
                # "top_p": 0.95,
                # "frequency_penalty": 0,
                # "presence_penalty": 0,
                # "stop": None,
            }
        if json_format is True:
            self.parameters['response_format'] = {'type': 'json_object'}

    def reset(self) -> None:
        """Reset the LLM class."""
        self.update_messages(reset=True)

    def update_messages(self, reset=False) -> None:
        """Update the messages list."""
        if self.past_message_num > 0 and not reset:
            self.messages = [self.messages[0]] + self.messages[1:][-self.past_message_num :]
        else:
            self.messages = [self.messages[0]]

    def query(self, user_prompt: str) -> str:
        """Query the LLM with the user prompt."""
        self.messages.append(
            {
                'role': 'user',
                'content': user_prompt,
            }
        )
        logger.info('Start to query %s with the following prompts:', self.name)
        logger.info(pprint.pformat(self.messages[-2:], width=120, compact=True))

        ans, timeout = '', 2
        retry = 4
        while not ans and retry > 0:
            try:
                retry -= 1
                time.sleep(timeout)
                response = completion(messages=self.messages, drop_params=True, **self.parameters)
                ans = response.choices[0].message.content
            except Exception as e:
                logger.info('%s', e)
            if not ans:
                timeout = timeout + 1 if timeout < 5 else timeout * 2
                logger.info('Will retry after %s seconds ...', timeout)

        logger.info('Query %s finished with the following answer:', self.name)
        logger.info('%s', ans)

        self.messages.append(
            {
                'role': 'assistant',
                'content': ans,
            }
        )
        self.update_messages()
        return ans
