#!/bin/bash

set -e  # Exit immediately on error.

source .venv/bin/activate
echo "==> Start to run SysCap CLI"

# check if .venv exists, if yes, remove it
if [ -d "../benchmarks/course_project_bench/.venv" ]; then
    echo "==> Removing existing .venv directory"
    rm -r ../benchmarks/course_project_bench/.venv
fi

if [ -d "../benchmarks/course_exam_bench/.venv" ]; then
    echo "==> Removing existing .venv directory"
    rm -r ../benchmarks/course_exam_bench/.venv
fi

if [ -d "../benchmarks/cache_bench/.venv" ]; then
    echo "==> Removing existing .venv directory"
    rm -r ../benchmarks/cache_bench/.venv
fi

if [ -d "../benchmarks/example_bench/.venv" ]; then
    echo "==> Removing existing .venv directory"
    rm -r ../benchmarks/example_bench/.venv
fi

python docker_run.py --benchmark_name "example_bench"
python docker_run.py --benchmark_name "course_exam_bench"
python docker_run.py --benchmark_name "cache_bench"
# course_project_bench needs docker to run (not supported yet)
python docker_run.py --benchmark_name "course_project_bench"

deactivate

echo "==> SysCap-CLI run completed successfully."
