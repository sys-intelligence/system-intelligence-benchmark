/*
 * clock.c - Portable timing routines using clock_gettime.
 *
 * Adapted from the original CS:APP Performance Lab timing code
 * to use POSIX clock_gettime(CLOCK_MONOTONIC) for portability
 * across x86, x86_64, ARM, and containerized environments.
 */

#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <time.h>
#include <sys/times.h>
#include "clock.h"

/*
 * Timing implementation using clock_gettime(CLOCK_MONOTONIC).
 * Returns elapsed time in nanoseconds, used as a proxy for "cycles"
 * by the fcyc measurement framework. Since all measurements are
 * ratios (speedups), the absolute unit does not matter.
 */

static struct timespec start_ts;

/* Record the current time */
void start_counter()
{
    clock_gettime(CLOCK_MONOTONIC, &start_ts);
}

/* Return nanoseconds elapsed since start_counter() was called */
double get_counter()
{
    struct timespec end_ts;
    clock_gettime(CLOCK_MONOTONIC, &end_ts);
    double elapsed = (double)(end_ts.tv_sec - start_ts.tv_sec) * 1e9
                   + (double)(end_ts.tv_nsec - start_ts.tv_nsec);
    if (elapsed < 0) {
        fprintf(stderr, "Error: counter returns negative value: %.0f\n", elapsed);
    }
    return elapsed;
}

/* Measure overhead of the timing routines themselves */
double ovhd()
{
    int i;
    double result;
    for (i = 0; i < 2; i++) {
        start_counter();
        result = get_counter();
    }
    return result;
}

/* Estimate the clock rate by measuring time during sleep */
double mhz_full(int verbose, int sleeptime)
{
    double rate;
    start_counter();
    sleep(sleeptime);
    rate = get_counter() / (1e6 * sleeptime);
    if (verbose)
        printf("Processor clock rate ~= %.1f MHz\n", rate);
    return rate;
}

double mhz(int verbose)
{
    return mhz_full(verbose, 2);
}

/*
 * Compensating counters - with clock_gettime, timer interrupt
 * compensation is not needed, so these just wrap the normal counters.
 */

void start_comp_counter()
{
    start_counter();
}

double get_comp_counter()
{
    return get_counter();
}
