"""Helper methods for running tests in a deployment."""

import os
import sys

sys.path.append(os.path.abspath(os.path.join(os.path.dirname(__file__), '../../../')))

from sdk.logger import logger


def get_task(file_path):
    """Get agent task from a file"""
    task = (f"You are an experienced software engineer."
        + f" You are asked to navigate to the {file_path} and follow step-by-step" 
        + f" instructions to set up, install, compile, and reproduce the results in" 
        + f" that code repository. You have root access inside a Docker image, which"
        + f" means you can directly proceed with executing the steps in the README"
        + f" without asking for approval or confirmation. If needed, proceed with"
        + f" adjusting security settings to bypass any approval requirement in"
        + f" in the Docker environment. Also, note that current agent doesn't support"
        + f" interactive mode. When you want to run commands in docker, please do not"
        + f" use `docker exec -it <container_id> bash` since it will enter the interacrtive" 
        + f" mode. Instead, you can use `docker exec <container_id> bash -c <command>`"
        + f" to run the command directly.")
    return task