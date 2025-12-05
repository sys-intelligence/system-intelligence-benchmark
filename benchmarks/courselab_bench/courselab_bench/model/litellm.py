import time
from typing import Any
import litellm
from loguru import logger


class LiteLLMModel:
    def __init__(self, model_name: str, temperature: float = 0.0, max_tokens: int = 4096, **kwargs):
        self.model_name = model_name
        self.temperature = temperature
        self.max_tokens = max_tokens
        self.kwargs = kwargs
        self.cost = 0.0
        self.n_calls = 0
        self.total_tokens = 0

    def query(self, messages: list[dict[str, Any]], max_retries: int = 3) -> dict[str, Any]:
        for attempt in range(max_retries):
            try:
                logger.debug(f"Querying {self.model_name} (attempt {attempt + 1}/{max_retries})")

                response = litellm.completion(
                    model=self.model_name,
                    messages=messages,
                    temperature=self.temperature,
                    max_tokens=self.max_tokens,
                    **self.kwargs,
                )

                content = response.choices[0].message.content
                self.n_calls += 1
                if hasattr(response, "usage") and response.usage:
                    tokens = response.usage.total_tokens
                    self.total_tokens += tokens

                    # Try to calculate cost (may not work for all models)
                    try:
                        cost = litellm.completion_cost(completion_response=response)
                        self.cost += cost
                        logger.debug(f"API call cost: ${cost:.6f}, tokens: {tokens}")
                    except Exception:
                        logger.debug(f"Could not calculate cost, tokens: {tokens}")
                else:
                    logger.debug("Token usage info not available")

                return {
                    "content": content,
                    "extra": {
                        "model": response.model if hasattr(response, "model") else None,
                        "usage": (
                            response.usage.model_dump() if hasattr(response, "usage") else None
                        ),
                    },
                }

            except Exception as e:
                logger.warning(f"API call failed (attempt {attempt + 1}/{max_retries}): {e}")

                if attempt < max_retries - 1:
                    # Exponential backoff: 2^attempt seconds
                    wait_time = 2**attempt
                    logger.info(f"Retrying in {wait_time}s...")
                    time.sleep(wait_time)
                else:
                    logger.error(f"API call failed after {max_retries} attempts")
                    raise RuntimeError(f"LiteLLM API call failed: {e}") from e

    def get_stats(self) -> dict[str, Any]:
        return {"cost": self.cost, "n_calls": self.n_calls, "tokens": self.total_tokens}
