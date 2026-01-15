package kvsrv

import (
	"log"
	"sync"
)

const Debug = false

func DPrintf(format string, a ...interface{}) (n int, err error) {
	if Debug {
		log.Printf(format, a...)
	}
	return
}

type Cache struct {
	seq   int
	value string
}

type KVServer struct {
	mu    sync.Mutex
	data  map[string]string
	cache map[int64]*Cache // client id -> seq ->value
}

func (kv *KVServer) Get(args *GetArgs, reply *GetReply) {
	kv.mu.Lock()
	defer kv.mu.Unlock()
	clientId, seqNum := args.ClientId, args.SeqNum
	key := args.Key
	reply.Value = ""
	// Either the client is new or the seqNum is greater than the cache seqNum.
	// In both cases, we can return the value directly.
	if ca, ok := kv.cache[clientId]; !ok || ca.seq <= seqNum {
		reply.Value = kv.data[key]
		return
	}
}

func (kv *KVServer) Put(args *PutAppendArgs, reply *PutAppendReply) {
	kv.mu.Lock()
	defer kv.mu.Unlock()
	clientId, seqNum := args.ClientId, args.SeqNum
	k, v := args.Key, args.Value
	reply.Value = ""
	if ca, ok := kv.cache[clientId]; ok && ca.seq >= seqNum {
		return
	} else if !ok {
		kv.cache[clientId] = new(Cache)
	}
	kv.data[k] = v
	kv.cache[clientId].seq = seqNum
	kv.cache[clientId].value = reply.Value
}

func (kv *KVServer) Append(args *PutAppendArgs, reply *PutAppendReply) {
	kv.mu.Lock()
	defer kv.mu.Unlock()
	clientId, seqNum := args.ClientId, args.SeqNum
	k, v := args.Key, args.Value
	reply.Value = ""
	// For ca.seq == seqNum, it means that the value has been appended.
	// However, the response might be lost, so we return the cache value.
	// For ca.seq > seqNum, it doesnt matter what the value is, just return.
	if ca, ok := kv.cache[clientId]; ok && ca.seq >= seqNum {
		reply.Value = ca.value
		return
	} else if !ok {
		kv.cache[clientId] = new(Cache)
	}
	reply.Value = kv.data[k]
	kv.cache[clientId].seq = seqNum
	kv.cache[clientId].value = kv.data[k]
	kv.data[k] += v
}

func StartKVServer() *KVServer {
	kv := new(KVServer)
	kv.data = make(map[string]string)
	kv.cache = make(map[int64]*Cache)
	return kv
}
