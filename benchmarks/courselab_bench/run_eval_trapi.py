#!/usr/bin/env python3
import os
from azure.identity import ChainedTokenCredential, AzureCliCredential, ManagedIdentityCredential
from inspect_ai import eval
from courselab import courselab

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
MAX_TURNS = 100
LIMIT = None
TASK_IDS = [
    "cmu_15-213__data_lab",
    "mit_6_5840_2024__kvraft_4a",
    "mit_6_5840_2024__kvraft_4b",
    "mit_6_5840_2024__kvsrv",
    "mit_6_5840_2024__kvsrv_2b",
    "mit_6_5840_2024__mapreduce",
    "mit_6_5840_2024__raft_3a",
    "mit_6_5840_2024__raft_3b",
    "mit_6_5840_2024__raft_3c",
    "mit_6_5840_2024__raft_3d",
    "mit_6_5840_2024__shardkv_5a",
    "mit_6_5840_2024__shardkv_5b",
]

if __name__ == "__main__":
    for trapi_model in TRAPI_MODELS:
        model = f"openai/azure/{trapi_model}"
        eval(
            tasks=courselab(task_ids=TASK_IDS, max_turns=MAX_TURNS),
            model=model,
            limit=LIMIT,
        )
