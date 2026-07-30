FROM ghcr.io/astral-sh/uv:python3.11-bookworm-slim AS builder

WORKDIR /workspace
COPY . /workspace
RUN mkdir -p /workspace/dist \
 && (uv build --package system-intelligence-sdk --wheel -o /workspace/dist || true) \
 && uv build --all-packages --wheel -o /workspace/dist

FROM ghcr.io/astral-sh/uv:python3.11-bookworm-slim

# Build with repository root as context:
# docker build -f benchmarks/cache_algo_bench/Dockerfile .
WORKDIR /workspace
COPY . /workspace
COPY --from=builder /workspace/dist/*.whl /tmp/dist/

WORKDIR /workspace/benchmarks/cache_algo_bench
RUN set -eux; \
 SDK_WHEEL="$(ls /tmp/dist/system_intelligence_sdk-*.whl | head -n1 || true)"; \
 BENCH_WHEEL="$(ls /tmp/dist/cache_algo_bench-*.whl | head -n1 || true)"; \
 if [ -z "$SDK_WHEEL" ]; then \
   echo "Missing SDK wheel in /tmp/dist. Build with repo root context:"; \
   echo "docker build -t cache_algo_bench -f benchmarks/cache_algo_bench/Dockerfile ."; \
   ls -1 /tmp/dist || true; \
   exit 1; \
 fi; \
 if [ -z "$BENCH_WHEEL" ]; then \
   echo "Missing cache_algo_bench wheel in /tmp/dist."; \
   ls -1 /tmp/dist || true; \
   exit 1; \
 fi; \
 rm -rf .venv; \
 uv venv .venv; \
 uv pip install --python .venv/bin/python "$SDK_WHEEL" "$BENCH_WHEEL"

# ENTRYPOINT ["./test.sh"]
