package kvraft

import (
	"crypto/rand"
	"math/big"
	"sync/atomic"
	"time"

	"6.5840/labrpc"
)

type Clerk struct {
	servers []*labrpc.ClientEnd
	cid     int64
	seq     int
	leader  int32 // cache the leader
}

func nrand() int64 {
	max := big.NewInt(int64(1) << 62)
	bigx, _ := rand.Int(rand.Reader, max)
	x := bigx.Int64()
	return x
}

func MakeClerk(servers []*labrpc.ClientEnd) *Clerk {
	ck := new(Clerk)
	ck.servers, ck.cid, ck.seq = servers, nrand(), 0
	return ck
}

// fetch the current value for a key.
// returns "" if the key does not exist.
// keeps trying forever in the face of all other errors.
//
// you can send an RPC with code like this:
// ok := ck.servers[i].Call("KVServer.Get", &args, &reply)
//
// the types of args and reply (including whether they are pointers)
// must match the declared types of the RPC handler function's
// arguments. and reply must be passed as a pointer.
func (ck *Clerk) Get(key string) string {
	ck.seq++

	args := new(GetArgs)
	args.Key, args.Cid, args.Seq = key, ck.cid, ck.seq

	leader := int(atomic.LoadInt32(&ck.leader))
	for {
		for i := 0; i < len(ck.servers); i++ {
			peer := (leader + i) % len(ck.servers)
			reply := new(GetReply)
			ok := ck.servers[peer].Call("KVServer.Get", args, reply)
			if ok && (reply.Err == OK || reply.Err == ErrNoKey) {
				atomic.StoreInt32(&ck.leader, int32(peer))
				return reply.Value
			}
		}
		time.Sleep(100 * time.Millisecond)
	}
}

// shared by Put and Append.
//
// you can send an RPC with code like this:
// ok := ck.servers[i].Call("KVServer.PutAppend", &args, &reply)
//
// the types of args and reply (including whether they are pointers)
// must match the declared types of the RPC handler function's
// arguments. and reply must be passed as a pointer.
func (ck *Clerk) PutAppend(key string, value string, op string) {
	ck.seq++

	args := new(PutAppendArgs)
	args.OpStr, args.Key, args.Value, args.Cid, args.Seq = op, key, value, ck.cid, ck.seq

	leader := int(atomic.LoadInt32(&ck.leader))
	for {
		for i := 0; i < len(ck.servers); i++ {
			peer := (leader + i) % len(ck.servers)
			reply := new(PutAppendReply)
			ok := ck.servers[peer].Call("KVServer.PutAppend", args, reply)
			if ok && reply.Err == OK {
				atomic.StoreInt32(&ck.leader, int32(peer))
				return
			}
		}
		time.Sleep(100 * time.Millisecond)
	}
}

func (ck *Clerk) Put(key string, value string) {
	ck.PutAppend(key, value, "Put")
}
func (ck *Clerk) Append(key string, value string) {
	ck.PutAppend(key, value, "Append")
}
