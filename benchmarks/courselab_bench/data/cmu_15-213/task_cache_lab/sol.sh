#!/bin/bash
set -euo pipefail
# Reference solution for CS:APP Cache Lab (csim.c + trans.c)

cat > csim.c << 'EOF'
#include "cachelab.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <getopt.h>
#include <limits.h>

// Cache line structure
typedef struct {
    int valid;
    int tag;
    int lru_counter;
} cache_line_t;

// Cache set structure
typedef struct {
    cache_line_t *lines;
} cache_set_t;

// Cache structure
typedef struct {
    int s; // number of set index bits
    int E; // number of lines per set
    int b; // number of block bits
    cache_set_t *sets;
} cache_t;

int verbose = 0;
int hit_count = 0;
int miss_count = 0;
int eviction_count = 0;

// Initialize the cache
cache_t* init_cache(int s, int E, int b) {
    cache_t *cache = malloc(sizeof(cache_t));
    cache->s = s;
    cache->E = E;
    cache->b = b;
    
    int S = 1 << s; // Number of sets
    cache->sets = calloc(S, sizeof(cache_set_t));
    
    for (int i = 0; i < S; i++) {
        cache->sets[i].lines = calloc(E, sizeof(cache_line_t));
    }
    
    return cache;
}

// Free the cache
void free_cache(cache_t *cache) {
    int S = 1 << cache->s;
    for (int i = 0; i < S; i++) {
        free(cache->sets[i].lines);
    }
    free(cache->sets);
    free(cache);
}

// Access the cache
void access_cache(cache_t *cache, unsigned long address) {
    unsigned long tag = address >> (cache->s + cache->b);
    unsigned long set_index = (address >> cache->b) & ((1 << cache->s) - 1);
    
    cache_set_t *set = &cache->sets[set_index];
    
    // Search for the block in the set
    int found = -1;
    for (int i = 0; i < cache->E; i++) {
        if (set->lines[i].valid && set->lines[i].tag == tag) {
            found = i;
            break;
        }
    }
    
    if (found != -1) {
        // Hit - update LRU counter
        hit_count++;
        if (verbose) {
            printf("hit ");
        }
        set->lines[found].lru_counter = 0;
        
        // Update other counters
        for (int i = 0; i < cache->E; i++) {
            if (i != found) {
                set->lines[i].lru_counter++;
            }
        }
    } else {
        // Miss
        miss_count++;
        if (verbose) {
            printf("miss ");
        }
        
        // Find empty line or victim using LRU
        int empty_line = -1;
        int victim_line = -1;
        int max_lru = -1;
        
        for (int i = 0; i < cache->E; i++) {
            if (!set->lines[i].valid) {
                empty_line = i;
                break;
            }
        }
        
        if (empty_line != -1) {
            // Use empty line
            set->lines[empty_line].valid = 1;
            set->lines[empty_line].tag = tag;
            set->lines[empty_line].lru_counter = 0;
            
            // Update other counters
            for (int i = 0; i < cache->E; i++) {
                if (i != empty_line) {
                    set->lines[i].lru_counter++;
                }
            }
        } else {
            // Evict victim using LRU
            for (int i = 0; i < cache->E; i++) {
                if (set->lines[i].lru_counter > max_lru) {
                    max_lru = set->lines[i].lru_counter;
                    victim_line = i;
                }
            }
            
            eviction_count++;
            if (verbose) {
                printf("eviction ");
            }
            
            set->lines[victim_line].tag = tag;
            set->lines[victim_line].lru_counter = 0;
            
            // Update other counters
            for (int i = 0; i < cache->E; i++) {
                if (i != victim_line) {
                    set->lines[i].lru_counter++;
                }
            }
        }
    }
}

int main(int argc, char *argv[]) {
    int s = 0, E = 0, b = 0;
    char *trace_file = NULL;
    int opt;
    
    while ((opt = getopt(argc, argv, "s:E:b:t:v")) != -1) {
        switch (opt) {
            case 's':
                s = atoi(optarg);
                break;
            case 'E':
                E = atoi(optarg);
                break;
            case 'b':
                b = atoi(optarg);
                break;
            case 't':
                trace_file = optarg;
                break;
            case 'v':
                verbose = 1;
                break;
            default:
                printf("./csim: Optional usage: -h, -v, -s <num>, -E <num>, -b <num>, -t <file>\n");
                exit(1);
        }
    }
    
    if (s <= 0 || E <= 0 || b <= 0 || trace_file == NULL) {
        printf("./csim: Missing required arguments\n");
        exit(1);
    }
    
    cache_t *cache = init_cache(s, E, b);
    
    FILE *fp = fopen(trace_file, "r");
    if (!fp) {
        printf("Error: Could not open file %s\n", trace_file);
        exit(1);
    }
    
    char operation;
    unsigned long address;
    int size;
    
    while (fscanf(fp, " %c %lx,%d", &operation, &address, &size) == 3) {
        if (verbose) {
            printf("%c %lx,%d ", operation, address, size);
        }
        
        switch (operation) {
            case 'L': // Load
            case 'S': // Store
                access_cache(cache, address);
                break;
            case 'M': // Modify (Load + Store)
                access_cache(cache, address);
                access_cache(cache, address);
                break;
        }
        
        if (verbose) {
            printf("\n");
        }
    }
    
    fclose(fp);
    free_cache(cache);
    
    printSummary(hit_count, miss_count, eviction_count);
    return 0;
}
EOF

cat > trans.c << 'EOF'
/* 
 * trans.c - Matrix transpose B = A^T
 *
 * Each transpose function must have a prototype of the form:
 * void trans(int M, int N, int A[N][M], int B[M][N]);
 *
 * A transpose function is evaluated by counting the number of misses
 * on a 1KB direct mapped cache with a block size of 32 bytes.
 */ 
#include <stdio.h>
#include "cachelab.h"

int is_transpose(int M, int N, int A[N][M], int B[M][N]);

/* 
 * transpose_submit - This is the solution transpose function that you
 *     will be graded on for Part B of the assignment. Do not change
 *     the description string "Transpose submission", as the driver
 *     searches for that string to identify the transpose function to
 *     be graded. 
 */
char transpose_submit_desc[] = "Transpose submission";
void transpose_submit(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, k, l;
    int temp0, temp1, temp2, temp3;

    if (M == 32 && N == 32) {
        // For 32x32 matrices, use 8x8 blocks
        for (i = 0; i < N; i += 8) {
            for (j = 0; j < M; j += 8) {
                // Process 8x8 block
                for (k = i; k < i + 8 && k < N; k++) {
                    for (l = j; l < j + 8 && l < M; l++) {
                        temp0 = A[k][l];
                        B[l][k] = temp0;
                    }
                }
            }
        }
    } else if (M == 64 && N == 64) {
        // For 64x64, we need to be very careful about cache conflicts
        // The direct-mapped cache with 32-byte blocks means every 16 integers,
        // elements will map to the same cache set when addressing is aligned
        for (i = 0; i < N; i += 8) {
            for (j = 0; j < M; j += 8) {
                // Work on 8x8 blocks, but subdivide them cleverly
                // First process upper-left 4x4
                for (k = i; k < i + 4; k++) {
                    temp0 = A[k][j]; temp1 = A[k][j+1]; temp2 = A[k][j+2]; temp3 = A[k][j+3];
                    B[j][k] = temp0; B[j+1][k] = temp1; B[j+2][k] = temp2; B[j+3][k] = temp3;
                }

                // Process lower-left 4x4 (rows i+4 to i+7, cols j to j+3)
                for (k = i + 4; k < i + 8; k++) {
                    temp0 = A[k][j]; temp1 = A[k][j+1]; temp2 = A[k][j+2]; temp3 = A[k][j+3];
                    B[j][k] = temp0; B[j+1][k] = temp1; B[j+2][k] = temp2; B[j+3][k] = temp3;
                }

                // Process upper-right 4x4 (rows i to i+3, cols j+4 to j+7)
                for (k = i; k < i + 4; k++) {
                    temp0 = A[k][j+4]; temp1 = A[k][j+5]; temp2 = A[k][j+6]; temp3 = A[k][j+7];
                    B[j+4][k] = temp0; B[j+5][k] = temp1; B[j+6][k] = temp2; B[j+7][k] = temp3;
                }

                // Process lower-right 4x4 (rows i+4 to i+7, cols j+4 to j+7)
                for (k = i + 4; k < i + 8; k++) {
                    temp0 = A[k][j+4]; temp1 = A[k][j+5]; temp2 = A[k][j+6]; temp3 = A[k][j+7];
                    B[j+4][k] = temp0; B[j+5][k] = temp1; B[j+6][k] = temp2; B[j+7][k] = temp3;
                }
            }
        }
    } else {
        // For other sizes like 61x67, use 16x16 blocks
        for (i = 0; i < N; i += 16) {
            for (j = 0; j < M; j += 16) {
                for (k = i; k < i + 16 && k < N; k++) {
                    for (l = j; l < j + 16 && l < M; l++) {
                        temp0 = A[k][l];
                        B[l][k] = temp0;
                    }
                }
            }
        }
    }
}

/* 
 * You can define additional transpose functions below. We've defined
 * a simple one below to help you get started. 
 */ 

/* 
 * trans - A simple baseline transpose function, not optimized for the cache.
 */
char trans_desc[] = "Simple row-wise scan transpose";
void trans(int M, int N, int A[N][M], int B[M][N])
{
    int i, j, tmp;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; j++) {
            tmp = A[i][j];
            B[j][i] = tmp;
        }
    }    

}

/*
 * registerFunctions - This function registers your transpose
 *     functions with the driver.  At runtime, the driver will
 *     evaluate each of the transpose functions and summarize their
 *     performance. This is a handy way to experiment with different
 *     transpose strategies.
 */
void registerFunctions()
{
    /* Register your solution function */
    registerTransFunction(transpose_submit, transpose_submit_desc); 

    /* Register any additional transpose functions */
    registerTransFunction(trans, trans_desc); 

}

/* 
 * is_transpose - This helper function checks if B is the transpose of
 *     A. You can check the correctness of your transpose by calling
 *     it before returning from the transpose function.
 */
int is_transpose(int M, int N, int A[N][M], int B[M][N])
{
    int i, j;

    for (i = 0; i < N; i++) {
        for (j = 0; j < M; ++j) {
            if (A[i][j] != B[j][i]) {
                return 0;
            }
        }
    }
    return 1;
}
EOF