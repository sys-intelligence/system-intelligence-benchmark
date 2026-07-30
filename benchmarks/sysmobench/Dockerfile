FROM ghcr.io/astral-sh/uv:python3.11-bookworm-slim AS builder

WORKDIR /workspace
COPY . /workspace
RUN mkdir -p /workspace/dist \
 && (uv build --package system-intelligence-sdk --wheel -o /workspace/dist || true) \
 && uv build --all-packages --wheel -o /workspace/dist

FROM ghcr.io/astral-sh/uv:python3.11-bookworm-slim

# Build with repository root as context:
# docker build -f benchmarks/sysmobench/Dockerfile .
WORKDIR /workspace
COPY . /workspace
COPY --from=builder /workspace/dist/*.whl /tmp/dist/

WORKDIR /workspace/benchmarks/sysmobench
RUN apt-get update && apt-get install -y --no-install-recommends openjdk-17-jdk git \
 && rm -rf /var/lib/apt/lists/*

RUN set -eux; \
 SDK_WHEEL="$(ls /tmp/dist/system_intelligence_sdk-*.whl | head -n1 || true)"; \
 BENCH_WHEEL="$(ls /tmp/dist/sysmobench_bench-*.whl | head -n1 || true)"; \
 if [ -z "$SDK_WHEEL" ]; then \
   echo "Missing SDK wheel in /tmp/dist. Build with repo root context:"; \
   echo "docker build -t sysmobench_bench -f benchmarks/sysmobench/Dockerfile ."; \
   ls -1 /tmp/dist || true; \
   exit 1; \
 fi; \
 if [ -z "$BENCH_WHEEL" ]; then \
   echo "Missing sysmobench_bench wheel in /tmp/dist."; \
   ls -1 /tmp/dist || true; \
   exit 1; \
 fi; \
 rm -rf .venv; \
 uv venv .venv; \
 uv pip install --python .venv/bin/python "$SDK_WHEEL" "$BENCH_WHEEL"; \
 uv pip install --python .venv/bin/python -e sysmobench_core; \
 .venv/bin/python sysmobench_core/tla_eval/setup_cli.py

# ENTRYPOINT ["./test.sh"]
