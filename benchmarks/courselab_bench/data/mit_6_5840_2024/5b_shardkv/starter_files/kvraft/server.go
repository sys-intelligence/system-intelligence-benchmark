package kvraft

import (
	"bytes"
	"log"
	"os"
	"sync"
	"sync/atomic"
	"time"

	"6.5840/labgob"
	"6.5840/labrpc"
	"6.5840/raft"
)

var Debug = os.Getenv("DEBUG") == "1"

func DPrintf(format string, a ...interface{}) (n int, err error) {
	if Debug {
		log.Printf(format, a...)
	}
	return
}

type Opcode int

const (
	GET Opcode = iota
	PUT
	APPEND
)

type Op struct {
	Cmd interface{}
	ClientInfo
}

type Done struct {
	index int
	term  int
	value string
	err   Err
}

type KVServer struct {
	mu      sync.Mutex
	me      int
	rf      *raft.Raft
	ps      *raft.Persister
	applyCh chan raft.ApplyMsg
	dead    int32 // set by Kill()

	maxraftstate int // snapshot if log grows this big

	data    map[string]string
	cache   map[int64]*Cache // client id -> seq
	chanmap map[int64]chan Done
}

func getChanId(term, index int) (id int64) {
	id = int64(term) << 32
	id += int64(index)
	return
}

func (kv *KVServer) makeChan(term, index int) chan Done {
	id := getChanId(term, index)
	ch := make(chan Done, 1)
	kv.chanmap[id] = ch
	return ch
}

func (kv *KVServer) closeAndDeleteChan(term, index int) {
	kv.mu.Lock()
	defer kv.mu.Unlock()
	id := getChanId(term, index)
	close(kv.chanmap[id])
	delete(kv.chanmap, id)
}

func (kv *KVServer) isCacheHit(Cid int64, Seq int) (bool, *Cache) {
	// Why cache.Seq >= Seq works?
	// 1. If the seq of cache equals to Seq, it means the operation has been
	//    executed. Return the value directly.
	// 2. If the seq of cache is Greater than Seq, it means some operations
	//    after this Op have been executed, which implies client has already
	//    received the result of this Op (the operation must be completed before
	//	  next operation happened). Theorically, return anything is OK.
	if cache, ok := kv.cache[Cid]; ok && cache.Seq >= Seq {
		return true, cache
	} else if ok {
		return false, cache
	} else {
		kv.cache[Cid] = new(Cache)
		return false, kv.cache[Cid]
	}
}

func (kv *KVServer) encode() []byte {
	w := new(bytes.Buffer)
	e := labgob.NewEncoder(w)
	e.Encode(kv.cache)
	e.Encode(kv.data)
	return w.Bytes()
}

func (kv *KVServer) decode(buf []byte) {
	if buf == nil || len(buf) < 1 {
		return
	}
	r := bytes.NewBuffer(buf)
	d := labgob.NewDecoder(r)
	var cache map[int64]*Cache
	var data map[string]string
	if d.Decode(&cache) != nil || d.Decode(&data) != nil {
		log.Fatal("Decode error")
		return
	}
	kv.cache = cache
	kv.data = data
}

func (kv *KVServer) startRaft(cmd interface{}, cid int64, seq int, ch chan *Cache) {
	kv.mu.Lock()
	defer kv.mu.Unlock()
	rr := new(Cache)
	if hit, cache := kv.isCacheHit(cid, seq); hit {
		rr.Seq, rr.Value, rr.Err = cache.Seq, cache.Value, cache.Err
		ch <- rr
	} else {
		op := new(Op)
		op.Cmd, op.Cid, op.Seq = cmd, cid, seq
		index, term, isLeader := kv.rf.Start(op)
		if !isLeader {
			cache.Value, cache.Err = "", ErrWrongLeader
			rr.Err = ErrWrongLeader
			ch <- rr
			return
		}
		donech := kv.makeChan(term, index)
		go kv.waitRaft(term, index, ch, donech)
		DPrintf("(startRaft) [%d] start raft with op %+v\n", kv.me, op)
	}
}

func (kv *KVServer) waitRaft(term, index int, ch chan *Cache, donech chan Done) {
	timer := time.NewTimer(500 * time.Millisecond)
	rr := new(Cache)
	DPrintf("(waitRaft) [%d] wait for term: %d, index: %d\n", kv.me, term, index)
	select {
	case <-timer.C:
		DPrintf("(waitRaft) [%d] timeout, term: %d, index: %d\n", kv.me, term, index)
		rr.Value = ""
		rr.Err = ErrWrongLeader
		ch <- rr
	case done := <-donech:
		rr.Value = done.value
		rr.Err = done.err
		ch <- rr
	}
	kv.closeAndDeleteChan(term, index)
}

func (kv *KVServer) raft(cmd interface{}, cid int64, seq int) *Cache {
	ch := make(chan *Cache)
	go kv.startRaft(cmd, cid, seq, ch)
	r := <-ch
	close(ch)
	return r
}

func (kv *KVServer) Get(args *GetArgs, reply *GetReply) {
	DPrintf("(Get) [%d] get %s\n", kv.me, args.Key)
	r := kv.raft(args, args.Cid, args.Seq)
	reply.Value = r.Value
	reply.Err = r.Err
}

func (kv *KVServer) PutAppend(args *PutAppendArgs, reply *PutAppendReply) {
	DPrintf("(PutAppend) [%d] %s %s: %s\n", kv.me, args.OpStr, args.Key, args.Value)
	r := kv.raft(args, args.Cid, args.Seq)
	reply.Err = r.Err
}

// Serializes the execution of operations on the key-value store.
func (kv *KVServer) executor() {
	for !kv.killed() {
		msg := <-kv.applyCh
		DPrintf("(executor) [%d] receive msg %+v\n", kv.me, msg)
		kv.mu.Lock()
		if msg.CommandValid {
			DPrintf("(executor) [%d] type of command: %T\n", kv.me, msg.Command)
			op := msg.Command.(*Op)
			index, term, cid, seq := msg.CommandIndex, msg.CommandTerm, op.Cid, op.Seq
			hit, cache := kv.isCacheHit(cid, seq)
			if !hit {
				cache.Seq, cache.Value, cache.Err = seq, "", OK
				switch v := op.Cmd.(type) {
				case *GetArgs:
					key := v.Key
					DPrintf("(executor) [%d] get %s: %s\n", kv.me, key, kv.data[key])
					if val, ok := kv.data[key]; ok {
						cache.Value = val
					} else {
						cache.Err = ErrNoKey
					}
				case *PutAppendArgs:
					if v.OpStr == "Put" {
						kv.data[v.Key] = v.Value
					} else if v.OpStr == "Append" {
						kv.data[v.Key] += v.Value
					}
					DPrintf("(executor) [%d] %s %s: %s\n", kv.me, v.OpStr, v.Key, kv.data[v.Key])
				}
				if kv.maxraftstate != -1 && kv.maxraftstate < kv.ps.RaftStateSize() {
					kv.rf.Snapshot(index, kv.encode())
				}
			}
			if ch, ok := kv.chanmap[getChanId(term, index)]; ok {
				select {
				case ch <- Done{index, term, cache.Value, cache.Err}:
				default:
					panic("Channel is full or closed")
				}
			}
		} else if msg.SnapshotValid {
			kv.decode(msg.Snapshot)
		} else {
			log.Fatalf("Invalid applyMsg, %+v\n", msg)
		}
		kv.mu.Unlock()
	}
}

// the tester calls Kill() when a KVServer instance won't
// be needed again. for your convenience, we supply
// code to set rf.dead (without needing a lock),
// and a killed() method to test rf.dead in
// long-running loops. you can also add your own
// code to Kill(). you're not required to do anything
// about this, but it may be convenient (for example)
// to suppress debug output from a Kill()ed instance.
func (kv *KVServer) Kill() {
	atomic.StoreInt32(&kv.dead, 1)
	kv.rf.Kill()
	// Your code here, if desired.
}

func (kv *KVServer) killed() bool {
	z := atomic.LoadInt32(&kv.dead)
	return z == 1
}

// servers[] contains the ports of the set of
// servers that will cooperate via Raft to
// form the fault-tolerant key/value service.
// me is the index of the current server in servers[].
// the k/v server should store snapshots through the underlying Raft
// implementation, which should call persister.SaveStateAndSnapshot() to
// atomically save the Raft state along with the snapshot.
// the k/v server should snapshot when Raft's saved state exceeds maxraftstate bytes,
// in order to allow Raft to garbage-collect its log. if maxraftstate is -1,
// you don't need to snapshot.
// StartKVServer() must return quickly, so it should start goroutines
// for any long-running work.
func StartKVServer(servers []*labrpc.ClientEnd, me int, persister *raft.Persister, maxraftstate int) *KVServer {
	// call labgob.Register on structures you want
	// Go's RPC library to marshall/unmarshall.
	labgob.Register(&Op{})
	labgob.Register(&GetArgs{})
	labgob.Register(&PutAppendArgs{})
	labgob.Register(&RaftReply{})
	labgob.Register(&Cache{})

	kv := new(KVServer)
	kv.me = me
	kv.maxraftstate = maxraftstate

	kv.applyCh = make(chan raft.ApplyMsg)
	kv.rf = raft.Make(servers, me, persister, kv.applyCh)
	kv.ps = persister
	kv.data = make(map[string]string)
	kv.cache = make(map[int64]*Cache)
	kv.chanmap = make(map[int64]chan Done)

	// Read from persister if any
	kv.decode(kv.ps.ReadSnapshot())

	go kv.executor()

	return kv
}
