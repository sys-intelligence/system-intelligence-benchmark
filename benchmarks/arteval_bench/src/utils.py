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
        + f" without asking for approval or confirmation. Once you rached the end"
        + f" of the README you must exit the Docker image gracefully.")
    return task