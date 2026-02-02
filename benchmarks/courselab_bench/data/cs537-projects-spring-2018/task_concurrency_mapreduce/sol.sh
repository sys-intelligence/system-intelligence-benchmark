#!/bin/bash
set -e

cd /workspace/ostep-projects/concurrency-mapreduce

cat > mapreduce.c <<'EOT'
#include "mapreduce.h"
#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct value_node {
    char *value;
    struct value_node *next;
} value_node;

typedef struct key_node {
    char *key;
    value_node *values_head;
    value_node *values_tail;
    value_node *iter;
    struct key_node *next;
} key_node;

typedef struct partition_state {
    pthread_mutex_t lock;
    key_node *keys;
    key_node **sorted_keys;
    int num_keys;
} partition_state;

static partition_state *partitions;
static int num_partitions;
static Partitioner partitioner_func;
static Mapper mapper_func;
static Reducer reducer_func;
static pthread_mutex_t file_lock = PTHREAD_MUTEX_INITIALIZER;
static int next_file;
static int num_files;
static char **file_names;

static void *map_thread(void *arg);
static void *reduce_thread(void *arg);
static char *get_next(char *key, int partition_number);
static int key_node_cmp(const void *a, const void *b);
static void free_partition(partition_state *partition);

void MR_Emit(char *key, char *value) {
    unsigned long partition_number = partitioner_func(key, num_partitions);
    partition_state *partition = &partitions[partition_number];

    pthread_mutex_lock(&partition->lock);

    key_node *current = partition->keys;
    while (current != NULL) {
        if (strcmp(current->key, key) == 0) {
            break;
        }
        current = current->next;
    }

    if (current == NULL) {
        current = malloc(sizeof(*current));
        if (current == NULL) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        current->key = strdup(key);
        if (current->key == NULL) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        current->values_head = NULL;
        current->values_tail = NULL;
        current->iter = NULL;
        current->next = partition->keys;
        partition->keys = current;
        partition->num_keys++;
    }

    value_node *value_entry = malloc(sizeof(*value_entry));
    if (value_entry == NULL) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    value_entry->value = strdup(value);
    if (value_entry->value == NULL) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }
    value_entry->next = NULL;

    if (current->values_tail == NULL) {
        current->values_head = value_entry;
        current->values_tail = value_entry;
    } else {
        current->values_tail->next = value_entry;
        current->values_tail = value_entry;
    }

    pthread_mutex_unlock(&partition->lock);
}

unsigned long MR_DefaultHashPartition(char *key, int num_partitions) {
    unsigned long hash = 5381;
    int c;

    while ((c = *key++) != '\0') {
        hash = hash * 33 + (unsigned long)c;
    }

    return hash % (unsigned long)num_partitions;
}

void MR_Run(int argc, char *argv[],
            Mapper map, int num_mappers,
            Reducer reduce, int num_reducers,
            Partitioner partition) {
    mapper_func = map;
    reducer_func = reduce;
    num_partitions = num_reducers;
    partitioner_func = partition == NULL ? MR_DefaultHashPartition : partition;
    num_files = argc - 1;
    file_names = argv + 1;
    next_file = 0;

    partitions = calloc((size_t)num_partitions, sizeof(*partitions));
    if (partitions == NULL) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }

    for (int i = 0; i < num_partitions; i++) {
        int rc = pthread_mutex_init(&partitions[i].lock, NULL);
        if (rc != 0) {
            fprintf(stderr, "mutex init failed\n");
            exit(1);
        }
        partitions[i].keys = NULL;
        partitions[i].sorted_keys = NULL;
        partitions[i].num_keys = 0;
    }

    pthread_t *mappers = malloc(sizeof(*mappers) * (size_t)num_mappers);
    if (mappers == NULL) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }

    for (int i = 0; i < num_mappers; i++) {
        pthread_create(&mappers[i], NULL, map_thread, NULL);
    }

    for (int i = 0; i < num_mappers; i++) {
        pthread_join(mappers[i], NULL);
    }

    free(mappers);

    pthread_t *reducers = malloc(sizeof(*reducers) * (size_t)num_reducers);
    if (reducers == NULL) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }

    for (int i = 0; i < num_reducers; i++) {
        int *partition_number = malloc(sizeof(*partition_number));
        if (partition_number == NULL) {
            fprintf(stderr, "out of memory\n");
            exit(1);
        }
        *partition_number = i;
        pthread_create(&reducers[i], NULL, reduce_thread, partition_number);
    }

    for (int i = 0; i < num_reducers; i++) {
        pthread_join(reducers[i], NULL);
    }

    free(reducers);

    for (int i = 0; i < num_partitions; i++) {
        pthread_mutex_destroy(&partitions[i].lock);
    }

    pthread_mutex_destroy(&file_lock);
    free(partitions);
    partitions = NULL;
}

static void *map_thread(void *arg) {
    (void)arg;

    while (1) {
        pthread_mutex_lock(&file_lock);
        if (next_file >= num_files) {
            pthread_mutex_unlock(&file_lock);
            break;
        }
        char *file = file_names[next_file++];
        pthread_mutex_unlock(&file_lock);

        mapper_func(file);
    }

    return NULL;
}

static void *reduce_thread(void *arg) {
    int partition_number = *(int *)arg;
    free(arg);

    partition_state *partition = &partitions[partition_number];
    if (partition->num_keys == 0) {
        return NULL;
    }

    partition->sorted_keys = malloc(sizeof(*partition->sorted_keys) * (size_t)partition->num_keys);
    if (partition->sorted_keys == NULL) {
        fprintf(stderr, "out of memory\n");
        exit(1);
    }

    int idx = 0;
    key_node *current = partition->keys;
    while (current != NULL) {
        partition->sorted_keys[idx++] = current;
        current = current->next;
    }

    qsort(partition->sorted_keys, (size_t)partition->num_keys, sizeof(*partition->sorted_keys), key_node_cmp);

    for (int i = 0; i < partition->num_keys; i++) {
        partition->sorted_keys[i]->iter = partition->sorted_keys[i]->values_head;
    }

    for (int i = 0; i < partition->num_keys; i++) {
        reducer_func(partition->sorted_keys[i]->key, get_next, partition_number);
    }

    free_partition(partition);

    return NULL;
}

static char *get_next(char *key, int partition_number) {
    partition_state *partition = &partitions[partition_number];

    for (int i = 0; i < partition->num_keys; i++) {
        key_node *node = partition->sorted_keys[i];
        if (strcmp(node->key, key) == 0) {
            value_node *value = node->iter;
            if (value == NULL) {
                return NULL;
            }
            node->iter = value->next;
            return value->value;
        }
    }

    return NULL;
}

static int key_node_cmp(const void *a, const void *b) {
    const key_node *left = *(const key_node *const *)a;
    const key_node *right = *(const key_node *const *)b;
    return strcmp(left->key, right->key);
}

static void free_partition(partition_state *partition) {
    for (int i = 0; i < partition->num_keys; i++) {
        key_node *node = partition->sorted_keys[i];
        value_node *value = node->values_head;
        while (value != NULL) {
            value_node *next_value = value->next;
            free(value->value);
            free(value);
            value = next_value;
        }
        free(node->key);
        free(node);
    }

    free(partition->sorted_keys);
    partition->sorted_keys = NULL;
    partition->keys = NULL;
    partition->num_keys = 0;
}
EOT
