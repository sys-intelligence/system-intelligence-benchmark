#!/bin/bash
set -euo pipefail

# Ensure the lab builds on 64-bit toolchains by removing -m32.
if grep -q "-m32" Makefile; then
  sed -i "s/ -m32//g" Makefile
fi

# Hash all read-only files to detect tampering during evaluation.
# Only mm.c may be modified by the student.
sha256sum \
  Makefile mdriver.c memlib.c memlib.h mm.h config.h \
  clock.c clock.h fcyc.c fcyc.h fsecs.c fsecs.h ftimer.c ftimer.h \
  short1-bal.rep short2-bal.rep \
  > .readonly_hashes
