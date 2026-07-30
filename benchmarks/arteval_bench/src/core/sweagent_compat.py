"""Compatibility helpers for SWE-agent wheels missing top-level runtime folders."""

from __future__ import annotations

import os
import shutil
from importlib.util import find_spec
from pathlib import Path


def prepare_sweagent_layout() -> tuple[Path, Path, Path]:
    """Create runtime directories expected by sweagent.__init__ if missing."""
    spec = find_spec('sweagent')
    if spec is None or spec.origin is None:
        raise RuntimeError('sweagent is not installed in the current environment')

    package_dir = Path(spec.origin).resolve().parent
    site_packages_dir = package_dir.parent
    config_dir = site_packages_dir / 'config'
    tools_dir = site_packages_dir / 'tools'
    trajectories_dir = site_packages_dir / 'trajectories'

    config_dir.mkdir(exist_ok=True)
    trajectories_dir.mkdir(exist_ok=True)

    if not tools_dir.exists():
        packaged_tools_dir = package_dir / 'tools'
        if packaged_tools_dir.is_dir():
            try:
                tools_dir.symlink_to(packaged_tools_dir, target_is_directory=True)
            except OSError:
                shutil.copytree(packaged_tools_dir, tools_dir)
        else:
            tools_dir.mkdir(exist_ok=True)

    return config_dir, tools_dir, trajectories_dir


def build_sweagent_env(base_env: dict[str, str] | None = None) -> dict[str, str]:
    """Build environment variables for sweagent runtime after layout prep."""
    config_dir, tools_dir, trajectories_dir = prepare_sweagent_layout()
    env = dict(os.environ if base_env is None else base_env)
    env.setdefault('SWE_AGENT_CONFIG_DIR', str(config_dir))
    env.setdefault('SWE_AGENT_TOOLS_DIR', str(tools_dir))
    env.setdefault('SWE_AGENT_TRAJECTORY_DIR', str(trajectories_dir))
    return env


def main() -> None:
    """CLI entrypoint for install/docker scripts."""
    config_dir, tools_dir, trajectories_dir = prepare_sweagent_layout()
    print(f'SWE-agent layout ready: config={config_dir} tools={tools_dir} trajectories={trajectories_dir}')


if __name__ == '__main__':
    main()
