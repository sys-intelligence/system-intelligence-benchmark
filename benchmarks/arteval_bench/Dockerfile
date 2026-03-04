FROM ghcr.io/astral-sh/uv:python3.11-bookworm-slim AS builder

WORKDIR /workspace
COPY . /workspace
RUN mkdir -p /workspace/dist \
 && (uv build --package system-intelligence-sdk --wheel -o /workspace/dist || true) \
 && uv build --all-packages --wheel -o /workspace/dist

FROM ghcr.io/astral-sh/uv:python3.11-bookworm-slim

ARG DEBIAN_FRONTEND=noninteractive
USER root
RUN apt-get update && apt-get install -y --no-install-recommends git \
 && rm -rf /var/lib/apt/lists/*

# Build with repository root as context:
# docker build -f benchmarks/arteval_bench/Dockerfile .
WORKDIR /workspace
COPY . /workspace
COPY --from=builder /workspace/dist/*.whl /tmp/dist/

WORKDIR /workspace/benchmarks/arteval_bench
RUN set -eux; \
 SDK_WHEEL="$(ls /tmp/dist/system_intelligence_sdk-*.whl | head -n1 || true)"; \
 BENCH_WHEEL="$(ls /tmp/dist/arteval_bench-*.whl | head -n1 || true)"; \
 if [ -z "$SDK_WHEEL" ]; then \
   echo "Missing SDK wheel in /tmp/dist. Build with repo root context:"; \
   echo "docker build -t arteval_bench -f benchmarks/arteval_bench/Dockerfile ."; \
   ls -1 /tmp/dist || true; \
   exit 1; \
 fi; \
 if [ -z "$BENCH_WHEEL" ]; then \
   echo "Missing arteval_bench wheel in /tmp/dist."; \
   ls -1 /tmp/dist || true; \
   exit 1; \
 fi; \
 rm -rf .venv; \
 uv venv .venv; \
 uv pip install --python .venv/bin/python "$SDK_WHEEL" "$BENCH_WHEEL"; \
 .venv/bin/python src/core/sweagent_compat.py >/dev/null; \
 .venv/bin/sweagent --help >/dev/null

CMD ["bash"]
