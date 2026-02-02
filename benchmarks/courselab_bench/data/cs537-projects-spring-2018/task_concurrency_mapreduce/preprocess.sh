#!/bin/bash
set -e

echo "=== Setting up CS537 Project 4a: MapReduce ==="

cd /workspace

echo "Installing git"
apt-get update > /dev/null 2>&1
apt-get install -y git > /dev/null 2>&1

echo "Cloning ostep-projects repository"
git clone https://github.com/remzi-arpacidusseau/ostep-projects.git > /dev/null 2>&1
cd ostep-projects
git checkout 76cff3f89f4bf337af6e02e53a831b7eeb1396df > /dev/null 2>&1

rm -rf .git

cd concurrency-mapreduce
mkdir -p tests

cat > tests/input1.txt <<'EOT'
foo bar foo
baz
EOT

cat > tests/input2.txt <<'EOT'
bar baz baz foo
EOT

cat > tests/input3.txt <<'EOT'
foo	bar
foo
qux qux qux
EOT

cat > tests/input_empty.txt <<'EOT'
EOT

cat > tests/input_copy.txt <<'EOT'
alpha
bravo
charlie
delta
echo
EOT

cat > tests/input_copy2.txt <<'EOT'
foxtrot
golf
hotel
EOT

cat > tests/mr_wordcount.c <<'EOT'
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mapreduce.h"

static void Map(char *file_name) {
    FILE *fp = fopen(file_name, "r");
    if (!fp) {
        perror("fopen");
        exit(1);
    }

    char *line = NULL;
    size_t size = 0;
    while (getline(&line, &size, fp) != -1) {
        char *cursor = line;
        char *token;
        while ((token = strsep(&cursor, " \t\r\n")) != NULL) {
            if (token[0] == '\0') {
                continue;
            }
            MR_Emit(token, "1");
        }
    }

    free(line);
    fclose(fp);
}

static void Reduce(char *key, Getter get_next, int partition_number) {
    int count = 0;
    char *value;
    (void)partition_number;

    while ((value = get_next(key, partition_number)) != NULL) {
        (void)value;
        count++;
    }

    printf("%s %d\n", key, count);
}

int main(int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "usage: %s <files...>\n", argv[0]);
        return 1;
    }

    MR_Run(argc, argv, Map, 4, Reduce, 3, MR_DefaultHashPartition);
    return 0;
}
EOT

cat > tests/mr_copytest.c <<'EOT'
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "mapreduce.h"

static void Map(char *file_name) {
    FILE *fp = fopen(file_name, "r");
    if (!fp) {
        perror("fopen");
        exit(1);
    }

    char *line = NULL;
    size_t size = 0;
    int idx = 0;
    while (getline(&line, &size, fp) != -1) {
        char keybuf[32];
        char valbuf[32];

        snprintf(keybuf, sizeof(keybuf), "line_%d", idx % 3);
        snprintf(valbuf, sizeof(valbuf), "%d", idx);

        MR_Emit(keybuf, valbuf);
        idx++;
    }

    free(line);
    fclose(fp);
}

static void Reduce(char *key, Getter get_next, int partition_number) {
    long sum = 0;
    char *value;
    (void)partition_number;

    while ((value = get_next(key, partition_number)) != NULL) {
        sum += strtol(value, NULL, 10);
    }

    printf("%s %ld\n", key, sum);
}

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "usage: %s <file>\n", argv[0]);
        return 1;
    }

    MR_Run(argc, argv, Map, 2, Reduce, 2, MR_DefaultHashPartition);
    return 0;
}
EOT

echo "Creating checksums for protected files"
mkdir -p /tmp/checksums
CHECKSUM_FILE=/tmp/checksums/protected.sha256
: > "$CHECKSUM_FILE"

PROTECTED_FILES=(
  "tests/input1.txt"
  "tests/input2.txt"
  "tests/input3.txt"
  "tests/input_empty.txt"
  "tests/input_copy.txt"
  "tests/input_copy2.txt"
  "tests/mr_wordcount.c"
  "tests/mr_copytest.c"
)

for file in "${PROTECTED_FILES[@]}"; do
  if [ -f "$file" ]; then
    sha256sum "$file" >> "$CHECKSUM_FILE"
    echo "  Protected: $file"
  fi
done

echo "Setup complete"
exit 0
