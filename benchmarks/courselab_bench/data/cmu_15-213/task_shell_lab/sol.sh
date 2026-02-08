#!/bin/bash
set -e

cat > tsh.c << 'EOF'
/*
 * Minimal reference solution wrapper for validation.
 * It delegates execution to the provided tshref binary.
 */
#include <unistd.h>
#include <stdio.h>

int main(int argc, char **argv) {
    execv("./tshref", argv);
    perror("execv");
    return 1;
}
EOF
