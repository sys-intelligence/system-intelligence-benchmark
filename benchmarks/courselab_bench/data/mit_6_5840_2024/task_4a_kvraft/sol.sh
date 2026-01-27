#!/bin/bash
set -e

git clone https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution
git -C /tmp/mit-solution checkout 95318f79101581ec37d04471e7c4d50d9cb2db3a

cp /tmp/mit-solution/src/kvraft/client.go src/kvraft/client.go
cp /tmp/mit-solution/src/kvraft/common.go src/kvraft/common.go
cp /tmp/mit-solution/src/kvraft/server.go src/kvraft/server.go

rm -rf /tmp/mit-solution
