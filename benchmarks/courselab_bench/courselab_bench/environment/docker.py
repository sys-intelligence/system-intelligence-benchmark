import subprocess
import uuid
from typing import Any
from pathlib import Path
from loguru import logger


class DockerEnvironment:
    def __init__(
        self,
        image: str,
        timeout: int = 60,
        work_dir: str = "/workspace",
        task_folder: Path | None = None,
    ):
        self.image = image
        self.timeout = timeout
        self.work_dir = work_dir
        self.container_id: str | None = None
        self.task_folder = task_folder

    def setup(self, task: dict[str, Any]) -> None:
        self.container_id = self._start_container()
        repo_url = task.get("repo_url")
        if repo_url:
            base_commit = task.get("base_commit")
            self._clone_repo(repo_url, base_commit)

        starter_files = task.get("starter_files")
        if starter_files and self.task_folder:
            self._copy_starter_files(starter_files)

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

    def _copy_starter_files(self, starter_files: list[dict[str, str]]) -> None:
        if not self.task_folder:
            raise RuntimeError("task_folder not set, cannot copy starter files")
        starter_files_dir = self.task_folder / "starter_files"
        if not starter_files_dir.exists():
            raise RuntimeError(f"starter_files directory not found: {starter_files_dir}")

        for file_spec in starter_files:
            src_rel = file_spec["src"]
            dest = file_spec["dest"]

            src_path = starter_files_dir / src_rel
            if not src_path.exists():
                raise RuntimeError(f"Starter file not found: {src_path}")

            logger.debug(f"Copying {src_path} to container:{dest}")

            parent_dir = str(Path(dest).parent)
            self.execute(f"mkdir -p {parent_dir}")
            cmd = [
                "docker",
                "cp",
                str(src_path),
                f"{self.container_id}:{dest}",
            ]

            try:
                _result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=60,
                    check=True,
                )
            except subprocess.CalledProcessError as e:
                raise RuntimeError(f"Failed to copy starter file {src_path}: {e.stderr}") from e

    def copy_output_files(self, output_files: list[dict[str, str]], output_dir: Path) -> None:
        if not self.container_id:
            raise RuntimeError("Container not started")

        output_dir.mkdir(parents=True, exist_ok=True)
        for file_spec in output_files:
            src = file_spec["src"]
            dest_rel = file_spec["dest"]
            dest_path = output_dir / dest_rel

            dest_path.parent.mkdir(parents=True, exist_ok=True)
            logger.debug(f"Copying container:{src} to {dest_path}")
            cmd = [
                "docker",
                "cp",
                f"{self.container_id}:{src}",
                str(dest_path),
            ]

            try:
                result = subprocess.run(
                    cmd,
                    capture_output=True,
                    text=True,
                    timeout=60,
                    check=False,  # Don't raise on error, file might not exist
                )
                if result.returncode != 0:
                    logger.warning(f"Failed to copy output file {src}: {result.stderr}")
            except Exception as e:
                logger.warning(f"Failed to copy output file {src}: {e}")
