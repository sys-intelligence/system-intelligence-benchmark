# CS:APP Performance Lab

## Overview

An image is represented as a two-dimensional matrix `M`, where `M[i][j]` denotes the value of the `(i,j)`th pixel of `M`. Pixel values are triples of red, green, and blue (RGB) values. Images are stored using the `pixel` data type defined in `defs.h`:

```c
typedef struct {
   unsigned short red;
   unsigned short green;
   unsigned short blue;
} pixel;
```

Images are stored in row-major order as a one-dimensional array. The pixel at row `i`, column `j` is accessed via the macro `RIDX(i, j, dim)` which computes `i * dim + j`.

Two image processing operations are provided:

- **Rotate**: Rotates an image counterclockwise by 90 degrees. The source pixel at position `(i,j)` is copied to position `(dim-1-j, i)` in the destination image.

- **Smooth**: Replaces each pixel with the average of all pixels in its neighborhood (a maximum of 3×3 area centered at that pixel). Pixels at the image boundary have a smaller neighborhood.

## Your Task

The file `kernels.c` contains naive implementations of `rotate()` and `smooth()`. Your job is to optimize these two functions to run as fast as possible while maintaining correctness. You should **only modify `kernels.c`**.

You may register multiple versions of each function using `add_rotate_function()` and `add_smooth_function()`. The driver will test all registered versions. However, only the functions named `rotate()` and `smooth()` will be graded.

**Important**: Do NOT modify any other files (`driver.c`, `defs.h`, `config.h`, `clock.c`, `clock.h`, `fcyc.c`, `fcyc.h`, `Makefile`). Only `kernels.c` should be changed.

## Building and Testing

```bash
make clean && make
./driver -t         # Run all benchmarks (skip team name check)
./driver -tg        # Autograder mode: test only rotate() and smooth()
```

The driver will test each registered function for correctness and measure its performance in Cycles Per Element (CPE). It computes a speedup ratio relative to the baseline CPE values in `config.h`.

## Grading

Your implementation will be graded on:
1. **Correctness**: Your optimized functions must produce identical results to the naive implementations.
2. **Performance**: You must achieve a geometric mean speedup of at least **1.5x** over the baseline for both `rotate()` and `smooth()`.

## Hints

- Think about cache-friendly memory access patterns. How are source and destination pixels accessed in memory?
- Consider loop transformations such as **blocking** (tiling) to improve spatial locality.
- Reduce function call overhead in performance-critical code paths.
- Avoid unnecessary conditional branches in inner loops — consider handling boundary cases separately.
- Understand how data is laid out in memory (row-major order) and how the CPU cache interacts with your access patterns.
- Loop unrolling can help reduce loop overhead and enable instruction-level parallelism.

## File Descriptions

| File | Description |
|------|-------------|
| `kernels.c` | **Your file to modify.** Contains `rotate()` and `smooth()` functions. |
| `driver.c` | Driver program that benchmarks your implementations. |
| `defs.h` | Pixel type definitions and function prototypes. |
| `config.h` | Baseline CPE measurements for computing speedup. |
| `clock.c`, `clock.h` | Timing routines. |
| `fcyc.c`, `fcyc.h` | k-best measurement scheme for reliable benchmarking. |
| `Makefile` | Build configuration. |
