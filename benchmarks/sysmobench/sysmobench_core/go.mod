module github.com/tla-eval/trace-generator

go 1.21

require (
	go.etcd.io/raft/v3 v3.5.12
)

replace go.etcd.io/raft/v3 => ./data/repositories/raft 