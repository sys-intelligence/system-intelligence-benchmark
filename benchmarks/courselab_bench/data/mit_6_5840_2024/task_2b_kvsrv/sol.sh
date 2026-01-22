#!/bin/bash
set -e

git clone --depth 1 https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution

cp /tmp/mit-solution/src/kvsrv/client.go src/kvsrv/client.go
cp /tmp/mit-solution/src/kvsrv/common.go src/kvsrv/common.go
cp /tmp/mit-solution/src/kvsrv/server.go src/kvsrv/server.go

rm -rf /tmp/mit-solution
