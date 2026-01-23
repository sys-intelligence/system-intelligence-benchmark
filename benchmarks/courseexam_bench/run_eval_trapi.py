#!/usr/bin/env python3
import os
from azure.identity import ChainedTokenCredential, AzureCliCredential, ManagedIdentityCredential
from inspect_ai import eval
from courseexam.courseexam import courseexam

TRAPI_APIPATH = os.environ.get("TRAPI_APIPATH", "redmond/interactive")
TRAPI_API_VERSION = os.environ.get("TRAPI_API_VERSION", "2025-04-01-preview")
TRAPI_ENDPOINT = os.environ.get("TRAPI_ENDPOINT", f"https://trapi.research.microsoft.com/{TRAPI_APIPATH}")
TRAPI_SCOPE = os.environ.get("TRAPI_SCOPE", "api://trapi/.default")

credential = ChainedTokenCredential(AzureCliCredential(), ManagedIdentityCredential())
token = credential.get_token(TRAPI_SCOPE)

# Set environment variables for inspect-ai
os.environ["AZUREAI_OPENAI_BASE_URL"] = TRAPI_ENDPOINT
os.environ["AZUREAI_OPENAI_API_VERSION"] = TRAPI_API_VERSION
os.environ["AZUREAI_OPENAI_API_KEY"] = token.token

TRAPI_MODELS = [
    "gpt-5.2_2025-12-11",
    "gpt-5-codex_2025-09-15",
    "o4-mini_2025-04-16"
]
TRAPI_JUDGE_MODEL = "gpt-4o_2024-11-20"
LIMIT = None
EXAM_IDS = None
QUESTION_TYPES = None
TAGS = None

if __name__ == "__main__":
    judge_model = f"openai/azure/{TRAPI_JUDGE_MODEL}"

    for trapi_model in TRAPI_MODELS:
        model = f"openai/azure/{trapi_model}"
        task = courseexam(
            exam_ids=EXAM_IDS,
            question_types=QUESTION_TYPES,
            tags=TAGS,
            judge_model=judge_model,
        )

        eval(tasks=task, model=model, limit=LIMIT)
