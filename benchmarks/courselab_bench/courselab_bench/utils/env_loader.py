import os
from pathlib import Path
from loguru import logger

try:
    import tomli
except ImportError:
    import tomllib as tomli  # Python 3.11+


def load_env_config(config_path: Path | str | None = None) -> dict:
    if config_path:
        env_file = Path(config_path)
    else:
        env_file = Path(".env.toml")
        if not env_file.exists():
            # Try project root
            project_root = Path(__file__).parent.parent.parent
            env_file = project_root / ".env.toml"

    if not env_file.exists():
        return {}

    try:
        with open(env_file, "rb") as f:
            config = tomli.load(f)

        for key, value in config.items():
            if value:  # Only set if value is not None/empty
                os.environ[key] = str(value)

        return config

    except Exception as e:
        logger.warning(f"Failed to load .env.toml: {e}")
        return {}
