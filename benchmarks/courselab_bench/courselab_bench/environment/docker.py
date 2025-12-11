import subprocess
import uuid
from typing import Any
from loguru import logger


class DockerEnvironment:
    def __init__(
        self,
        image: str,
        timeout: int = 60,
        work_dir: str = "/workspace",
    ):
        self.image = image
        self.timeout = timeout
        self.work_dir = work_dir
        self.container_id: str | None = None

    def setup(self, task: dict[str, Any]) -> None:
        self.container_id = self._start_container()
        repo_url = task.get("repo_url")
        if repo_url:
            base_commit = task.get("base_commit")
            self._clone_repo(repo_url, base_commit)

        preprocess_script = task.get("preprocess_script")
        if preprocess_script:
            self._run_preprocess(preprocess_script)

    def execute(self, command: str, timeout: int | None = None) -> dict[str, Any]:
        if not self.container_id:
            raise RuntimeError("Container not started. Call setup() first.")

        cmd = [
            "docker",
            "exec",
            "-w",
            self.work_dir,  # Set working directory
            self.container_id,
            "bash",
            "-lc",  # Login shell to load environment
            command,
        ]

        logger.debug(f"Executing: {command[:100]}...")

        try:
            result = subprocess.run(
                cmd,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,  # Combine stdout and stderr
                text=True,
                encoding="utf-8",
                errors="replace",  # Replace invalid unicode
                timeout=timeout or self.timeout,
            )

            logger.debug(f"Command finished with exit code: {result.returncode}")

            return {"output": result.stdout, "returncode": result.returncode}

        except subprocess.TimeoutExpired as e:
            # Re-raise with stdout for agent to handle
            logger.error(f"Command timed out after {timeout or self.timeout}s")
            if isinstance(e.stdout, str):
                e.stdout = e.stdout.encode("utf-8")
            elif e.stdout is None:
                e.stdout = b""
            raise
        except Exception as e:
            logger.error(f"Command execution failed: {e}")
            return {"output": f"[ERROR: {type(e).__name__}: {str(e)}]", "returncode": 1}

    def cleanup(self) -> None:
        if not self.container_id:
            return

        # Run cleanup in background with timeout (similar to mini-swe-agent)
        cmd = f"(timeout 60 docker stop {self.container_id} || docker rm -f {self.container_id}) >/dev/null 2>&1 &"

        try:
            subprocess.Popen(cmd, shell=True)
        except Exception:
            pass  # Ignore cleanup errors
        finally:
            self.container_id = None

    def __del__(self):
        self.cleanup()

    def _start_container(self) -> str:
        container_name = f"courselab-{uuid.uuid4().hex[:8]}"
        cmd = [
            "docker",
            "run",
            "-d",  # Detached mode
            "-it",  # Interactive with TTY
            "--rm",  # Auto-remove when stopped
            "--name",
            container_name,
            "-w",
            self.work_dir,  # Set working directory
            self.image,
            "sleep",
            "7200",  # Keep container alive for 2 hours
        ]

        logger.debug(f"Starting container: {' '.join(cmd)}")

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=300,  # 5 minutes to pull image if needed (will we ever need longer?)
                check=True,
            )
            container_id = result.stdout.strip()
            return container_id
        except subprocess.TimeoutExpired as e:
            raise RuntimeError("Docker container start timed out") from e
        except subprocess.CalledProcessError as e:
            raise RuntimeError(f"Failed to start Docker container: {e.stderr}") from e
        except FileNotFoundError:
            raise RuntimeError("Docker is not installed or not in PATH")

    def _clone_repo(self, repo_url: str, base_commit: str | None = None) -> None:
        clone_result = self.execute(f"git clone {repo_url} {self.work_dir}", timeout=300)

        if clone_result["returncode"] != 0:
            raise RuntimeError(f"Failed to clone repository: {clone_result['output'][:200]}")

        if base_commit:
            checkout_result = self.execute(f"cd {self.work_dir} && git checkout {base_commit}")

            if checkout_result["returncode"] != 0:
                raise RuntimeError(
                    f"Failed to checkout commit {base_commit}: {checkout_result['output'][:200]}"
                )

    def _run_preprocess(self, preprocess_script: str) -> None:
        script_path = f"{self.work_dir}/preprocess.sh"
        self.execute(
            f"cat > {script_path} << 'PREPROCESS_EOF'\n{preprocess_script}\nPREPROCESS_EOF"
        )
        self.execute(f"chmod +x {script_path}")
        result = self.execute(f"cd {self.work_dir} && bash {script_path}")

        if result["returncode"] != 0:
            raise RuntimeError(f"Preprocess script failed: {result['output'][:200]}")
