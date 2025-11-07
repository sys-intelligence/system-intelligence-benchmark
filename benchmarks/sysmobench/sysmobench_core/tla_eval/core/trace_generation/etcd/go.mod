module github.com/etcd-io/tla-benchmark/trace-generator

go 1.24

toolchain go1.24.5

// Use the local raft repository
replace go.etcd.io/raft/v3 => ../../../../data/repositories/etcd

require go.etcd.io/raft/v3 v3.0.0-00010101000000-000000000000

require (
	github.com/gogo/protobuf v1.3.2 // indirect
	github.com/golang/protobuf v1.5.4 // indirect
	google.golang.org/protobuf v1.33.0 // indirect
)
