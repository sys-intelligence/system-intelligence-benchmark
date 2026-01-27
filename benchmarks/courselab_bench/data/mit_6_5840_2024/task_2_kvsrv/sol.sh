#!/bin/bash
set -e

git clone https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution
git -C /tmp/mit-solution checkout 95318f79101581ec37d04471e7c4d50d9cb2db3a

cp /tmp/mit-solution/src/kvsrv/client.go src/kvsrv/client.go
cp /tmp/mit-solution/src/kvsrv/common.go src/kvsrv/common.go
cp /tmp/mit-solution/src/kvsrv/server.go src/kvsrv/server.go

rm -rf /tmp/mit-solution
