package kvsrv

type PutAppendArgs struct {
	Key      string
	Value    string
	ClientId int64
	SeqNum   int
}

type PutAppendReply struct {
	Value string
}

type GetArgs struct {
	Key      string
	ClientId int64
	SeqNum   int
}

type GetReply struct {
	Value string
}
