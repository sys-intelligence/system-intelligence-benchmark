#!/bin/bash
set -e

git clone --depth 1 https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution

cp /tmp/mit-solution/src/raft/append_entries.go src/raft/append_entries.go
cp /tmp/mit-solution/src/raft/election.go src/raft/election.go
cp /tmp/mit-solution/src/raft/install_snapshot.go src/raft/install_snapshot.go
cp /tmp/mit-solution/src/raft/raft.go src/raft/raft.go
cp /tmp/mit-solution/src/raft/util.go src/raft/util.go

rm -rf /tmp/mit-solution
