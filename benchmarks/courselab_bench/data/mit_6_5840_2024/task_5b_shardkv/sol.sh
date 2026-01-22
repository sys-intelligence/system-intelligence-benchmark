#!/bin/bash
set -e

git clone --depth 1 https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution

cp /tmp/mit-solution/src/shardctrler/client.go src/shardctrler/client.go
cp /tmp/mit-solution/src/shardctrler/common.go src/shardctrler/common.go
cp /tmp/mit-solution/src/shardctrler/server.go src/shardctrler/server.go
cp /tmp/mit-solution/src/shardkv/client.go src/shardkv/client.go
cp /tmp/mit-solution/src/shardkv/common.go src/shardkv/common.go
cp /tmp/mit-solution/src/shardkv/server.go src/shardkv/server.go

rm -rf /tmp/mit-solution
