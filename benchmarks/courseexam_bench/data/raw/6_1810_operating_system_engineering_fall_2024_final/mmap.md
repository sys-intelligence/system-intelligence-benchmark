```c
#include <stdlib.h>
#include <stdio.h>
#include <errno.h>
#include <unistd.h>
#include <string.h>
#include <signal.h>
#include <stdint.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/time.h>
#include <math.h>

static size_t page_size;

// align_down - rounds a value down to an alignment
// @x: the value
// @a: the alignment (must be power of 2)
//
// Returns an aligned value.
#define align_down(x, a)((x) & ˜((typeof (x))(a) - 1))
#define AS_LIMIT #define MAX_SQRTS static double * sqrts;
(1 << 23) // Maximum limit on virtual memory bytes
(1 << 27) // Maximum limit on sqrt table entries
static int nfault;
// Use this helper function as an oracle for square root values.
static void
calculate_sqrts(double * sqrt_pos, int start, int nr) {
  int i;
  for (i = 0; i < nr; i++)
    sqrt_pos[i] = sqrt((double)(start + i));
}
static void
handle_sigsegv(int sig, siginfo_t * si, void * ctx) {
  uintptr_t fault_addr = (uintptr_t) si -> si_addr;
  double * page_base = (double * ) align_down(fault_addr, page_size);
  static double * last_page_base = NULL;
  if (last_page_base && munmap(last_page_base, page_size) == -1) {
    fprintf(stderr, "Couldn’t munmap(); %s\n", strerror(errno));
    exit(EXIT_FAILURE);
  }
  if (mmap(page_base, page_size, PROT_READ | PROT_WRITE,
      MAP_PRIVATE | MAP_ANONYMOUS | MAP_FIXED, -1, 0) == MAP_FAILED) {
    fprintf(stderr, "Couldn’t mmap(); %s\n", strerror(errno));
    exit(EXIT_FAILURE);
  }
  nfault++;
  calculate_sqrts(page_base, page_base - sqrts, page_size / sizeof(double));
  last_page_base = page_base;
}
static void
setup_sqrt_region(void) {
  struct rlimit lim = {
    AS_LIMIT,
    AS_LIMIT
  };
  struct sigaction act;
  // Only mapping to find a safe location for the table.
  sqrts = mmap(NULL, MAX_SQRTS * sizeof(double) + AS_LIMIT, PROT_NONE,
    MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
  if (sqrts == MAP_FAILED) {
    fprintf(stderr, "Couldn’t mmap() region for sqrt table; %s\n",
      strerror(errno));
    exit(EXIT_FAILURE);
  }
  // Now release the virtual memory to remain under the rlimit.
  if (munmap(sqrts, MAX_SQRTS * sizeof(double) + AS_LIMIT) == -1) {
    fprintf(stderr, "Couldn’t munmap() region for sqrt table; %s\n",
      strerror(errno));
    exit(EXIT_FAILURE);
  }
  // Set a soft rlimit on virtual address-space bytes.
  if (setrlimit(RLIMIT_AS, & lim) == -1) {
    fprintf(stderr, "Couldn’t set rlimit on RLIMIT_AS; %s\n", strerror(errno));
    exit(EXIT_FAILURE);
  }
  // Register a signal handler to capture SIGSEGV.
  act.sa_sigaction = handle_sigsegv;
  act.sa_flags = SA_SIGINFO;
  sigemptyset( & act.sa_mask);
  if (sigaction(SIGSEGV, & act, NULL) == -1) {
    fprintf(stderr, "Couldn’t set up SIGSEGV handler;, %s\n", strerror(errno));
    exit(EXIT_FAILURE);
  }
}
static void
test_sqrt_region(void) {
  int i, pos = rand() % (MAX_SQRTS - 1);
  double correct_sqrt;
  struct timeval start, end;
  long secs_used, micros_used;
  printf("Validating square root table contents...\n");
  srand(0xDEADBEEF);
  gettimeofday( & start, NULL);
  for (i = 0; i < 1000; i++) {
    pos = rand() % (MAX_SQRTS - 1);
    calculate_sqrts( & correct_sqrt, pos, 1);
    if (sqrts[pos] != correct_sqrt) {
      fprintf(stderr, "Square root is incorrect. Expected %f, got %f.\n",
        correct_sqrt, sqrts[pos]);
      exit(EXIT_FAILURE);
    }
  }
  gettimeofday( & end, NULL);
  printf("start: %d secs, %d usecs\n", start.tv_sec, start.tv_usec);
  printf("end: %d secs, %d usecs\n", end.tv_sec, end.tv_usec);
  secs_used = (end.tv_sec - start.tv_sec); //avoid overflow by subtracting first
  micros_used = ((secs_used * 1000000) + end.tv_usec) - (start.tv_usec);
  printf("micros_used: %d for nfault %d\n", micros_used, nfault);
}
int
main(int argc, char * argv[]) {
  page_size = sysconf(\_SC_PAGESIZE);
  printf("page_size is %ld\n", page_size);
  setup_sqrt_region();
  test_sqrt_region();
  return 0;
}
```
