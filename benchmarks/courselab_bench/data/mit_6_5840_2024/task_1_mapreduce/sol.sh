#!/bin/bash
set -e

# Clone the reference solution repository
git clone --depth 1 https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution

# Copy the solution files to the task directory
cp /tmp/mit-solution/src/mr/coordinator.go src/mr/coordinator.go
cp /tmp/mit-solution/src/mr/rpc.go src/mr/rpc.go
cp /tmp/mit-solution/src/mr/worker.go src/mr/worker.go

# Clean up
rm -rf /tmp/mit-solution
