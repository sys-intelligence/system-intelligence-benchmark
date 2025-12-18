package kvraft

const (
	OK             = "OK"
	ErrNoKey       = "ErrNoKey"
	ErrWrongLeader = "ErrWrongLeader"
)

type ClientInfo struct {
	Cid int64
	Seq int
}

type Err string

type RaftReply struct {
	Value string
	Err   Err
}

type GetArgs struct {
	Key string
	ClientInfo
}

type GetReply = RaftReply

// Put or Append
type PutAppendArgs struct {
	OpStr string // "Put" or "Append"
	Key   string
	Value string
	ClientInfo
}

type PutAppendReply = RaftReply

type Cache struct {
	Seq int
	RaftReply
}
