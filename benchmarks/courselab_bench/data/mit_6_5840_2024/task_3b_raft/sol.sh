#!/bin/bash
set -e

git clone https://github.com/GaryHo34/MIT-6.5840-distributed-systems-labs.git /tmp/mit-solution
git -C /tmp/mit-solution checkout 95318f79101581ec37d04471e7c4d50d9cb2db3a

cp /tmp/mit-solution/src/raft/append_entries.go src/raft/append_entries.go
cp /tmp/mit-solution/src/raft/election.go src/raft/election.go
cp /tmp/mit-solution/src/raft/install_snapshot.go src/raft/install_snapshot.go
cp /tmp/mit-solution/src/raft/raft.go src/raft/raft.go
cp /tmp/mit-solution/src/raft/util.go src/raft/util.go

rm -rf /tmp/mit-solution
