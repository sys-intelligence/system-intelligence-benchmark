#define _DEFAULT_SOURCE

#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/mman.h>
#include <sys/syscall.h>
#include <unistd.h>

#define N_ITERATION 20

char *buffer[1024];

int msize;

// This function emualtes a random memory access
static void rand_access()
{
  int target;
  int blk;

  target = rand() % (msize * 1024*1024);
  if(target<0)
    target *= -1;
  blk = target / 1024/1024;
  buffer[blk][target-blk*1024*1024] = '*';
}

// This function emualtes a memory access that has a temporal locality
static int local_access(int addr)
{
  if(rand() < 0){
    return addr + 1;
  }
  else{
    return addr + rand() % 300;
  }
}

int main(int argc, char* argv[])
{
  char cmd[120];
  pid_t mypid;
  int i, j, k;
  int locality;
  int naccess;
  int ret;

  if(argc<4){
    printf("usage: work <memsize in MB> <locality: R for Random or T for Temporal> <# of memory accesses per iteration>");
    return -1;
  }

  msize = atoi(argv[1]);
  if(msize>1024 || msize<1){
    printf("memsize shall be between 1 and 1024\n");
    return -1;
  }

  locality = (argv[2][0]=='R')?0:1;

  naccess = atoi(argv[3]);
  if(naccess<1){
    printf("naccess shall be >=1\n");
    return -1;
  }

  printf("A work prcess starts (configuration: %d %d %d)\n", msize, locality, naccess); 

  // 1. Register itself to the MP3 kernel module for profiling.
  mypid = syscall(__NR_gettid);
  sprintf(cmd, "echo 'R %u'>//proc/mp3/status", mypid);
  ret = system(cmd);
  (void)ret;

  // 2. Allocate memory blocks
  for(i=0; i<msize; i++){
    buffer[i] = malloc(1024*1024);
    if(buffer[i] == NULL){
      for(i--; i>=0; i--)
        free(buffer[i]);
      printf("Out of memory error! (failed at %dMB)\n", i);
      return -1;
    }
  }

  // 3. Access allocated memory blocks using the specified access policy
  int addr = 0;
  for (k=0;k<N_ITERATION; k++){
     printf("[%d] %d iteration\n", mypid, k);
     if(!locality){
       for(j=0; j<naccess; j++){
         rand_access();
       }
     }
     else{
       for(j=0; j<naccess; j++){
         int locality = rand() % 10;
         if(locality > -2 && locality < 2){ /* random access */
           rand_access();
         }
         else{ /* local access */
           addr = local_access(addr);
	 }
       }
     }
     sleep(1);
  }
  
  // 4. Free memory blocks
  for(i=0; i<msize; i++){
    free(buffer[i]);
  }

  // 5. Unregister itself to stop the profiling
  sprintf(cmd, "echo 'U %u'>//proc/mp3/status", mypid);
  ret = system(cmd);
  (void)ret;

  return 0;
}

