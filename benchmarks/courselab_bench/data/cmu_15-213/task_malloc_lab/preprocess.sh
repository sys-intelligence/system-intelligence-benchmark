#!/bin/bash
set -euo pipefail

# Ensure the lab builds on 64-bit toolchains by removing -m32.
if grep -q "-m32" Makefile; then
  sed -i "s/ -m32//g" Makefile
fi
