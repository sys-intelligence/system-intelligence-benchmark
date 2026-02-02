***********************
CS:APP Cache Lab (15-213)
***********************

Your job is to implement the cache simulator and cache-friendly transpose in the starter. Edit **only** the two solution files:

- csim.c — LRU cache simulator for the given traces
- trans.c — Cache-optimized matrix transpose (fill in transpose_submit)

Build and test
==============

1. Build everything: `make`
2. Simulator check: `./test-csim`
3. Transpose check and perf: `./test-trans -M 32 -N 32`, `./test-trans -M 64 -N 64`, `./test-trans -M 61 -N 67`

Notes
=====

- Do not modify cachelab.c/h, the traces, or the Makefile.
- `valgrind` is available in the container; test-trans will invoke it for validation.
- Keep output reasonable; only csim.c and trans.c are collected as artifacts.
