#!/bin/bash
set -e

if [ -f result.txt ]; then
    rm result.txt
fi

echo "Preprocessing complete"
exit 0
