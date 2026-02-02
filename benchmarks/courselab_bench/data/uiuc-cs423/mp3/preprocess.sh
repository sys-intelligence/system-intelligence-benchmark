#!/usr/bin/env bash
set -euo pipefail

WORKDIR="/workspace"
cd "$WORKDIR"

rm -f auto_grade.txt autograde.txt 2>/dev/null || true
