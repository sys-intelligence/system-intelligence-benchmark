#!/bin/bash
set -e

git clone --depth 1 https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution

cp /tmp/mit-solution/src/kvraft/client.go src/kvraft/client.go
cp /tmp/mit-solution/src/kvraft/common.go src/kvraft/common.go
cp /tmp/mit-solution/src/kvraft/server.go src/kvraft/server.go

rm -rf /tmp/mit-solution
