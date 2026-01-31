#!/bin/bash
set -e

git clone https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution
git -C /tmp/mit-solution checkout 95318f79101581ec37d04471e7c4d50d9cb2db3a

cp /tmp/mit-solution/src/shardctrler/client.go src/shardctrler/client.go
cp /tmp/mit-solution/src/shardctrler/common.go src/shardctrler/common.go
cp /tmp/mit-solution/src/shardctrler/server.go src/shardctrler/server.go
cp /tmp/mit-solution/src/shardkv/client.go src/shardkv/client.go
cp /tmp/mit-solution/src/shardkv/common.go src/shardkv/common.go
cp /tmp/mit-solution/src/shardkv/server.go src/shardkv/server.go

rm -rf /tmp/mit-solution
