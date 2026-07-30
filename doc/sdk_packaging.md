# SDK Packaging Guide

This guide covers how to build and (optionally) publish the standalone `system-intelligence-sdk` package.

## Package Location
- Project metadata: `pyproject.toml` (repository root)
- Package code: `sdk/*.py`

## Local Build
From repository root:

```bash
uv build --package system-intelligence-sdk --wheel --sdist
uv run python -m twine check dist/system_intelligence_sdk-*
```

Expected artifacts:
- `dist/system_intelligence_sdk-<version>.tar.gz`
- `dist/system_intelligence_sdk-<version>-py3-none-any.whl`

## Local Editable Install
```bash
uv sync --extra dev
```

## Release Flow (Recommended)
1. Bump version in root `pyproject.toml`.
2. Open PR and ensure `SDK Package` workflow passes.
3. Create a release tag after merge.
4. Publish from CI using trusted publisher or a `PYPI_API_TOKEN` secret.

## Notes
- In network-restricted environments, local build/install may fail while resolving build dependencies (`uv_build`, `build`).
- CI should be treated as the source of truth for package build validation.
