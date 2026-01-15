package raft

//
// this is an outline of the API that raft must expose to
// the service (or tester). see comments below for
// each of these functions for more details.
//
// rf = Make(...)
//   create a new Raft server.
// rf.Start(command interface{}) (index, term, isleader)
//   start agreement on a new log entry
// rf.GetState() (term, isLeader)
//   ask a Raft for its current term, and whether it thinks it is leader
// ApplyMsg
//   each time a new entry is committed to the log, each Raft peer
//   should send an ApplyMsg to the service (or tester)
//   in the same server.
//

import (
	//	"bytes"

	"bytes"
	"log"
	"sync"
	"sync/atomic"
	"time"

	//	"6.5840/labgob"
	"6.5840/labgob"
	"6.5840/labrpc"
)

// as each Raft peer becomes aware that successive log entries are
// committed, the peer should send an ApplyMsg to the service (or
// tester) on the same server, via the applyCh passed to Make(). set
// CommandValid to true to indicate that the ApplyMsg contains a newly
// committed log entry.
//
// in part 3D you'll want to send other kinds of messages (e.g.,
// snapshots) on the applyCh, but set CommandValid to false for these
// other uses.
type ApplyMsg struct {
	CommandValid bool
	Command      interface{}
	CommandIndex int
	CommandTerm  int

	// For 3D:
	SnapshotValid bool
	Snapshot      []byte
	SnapshotTerm  int
	SnapshotIndex int
}

type Entry struct {
	Term    int
	Index   int
	Command interface{}
}

// Base struct for common fields
type BaseRPC struct {
	Term int
}

// Implement RaftRPC interface for BaseRPC
func (b *BaseRPC) GetTerm() int {
	return b.Term
}

func (b *BaseRPC) SetTerm(term int) {
	b.Term = term
}

// RaftRPC interface
type RaftRPC interface {
	GetTerm() int
	SetTerm(int)
}

type ServerState int

const (
	FOLLOWER ServerState = iota
	CANDIDATE
	LEADER
)

// A Go object implementing a single Raft peer.
type Raft struct {
	mu                sync.Mutex          // Lock to protect shared access to this peer's state
	peers             []*labrpc.ClientEnd // RPC end points of all peers
	persister         *Persister          // Object to hold this peer's persisted state
	me                int                 // this peer's index into peers[]
	dead              int32               // set by Kill()
	heartbeatTimeout  time.Duration
	electionTimeout   time.Duration
	electionTimeStamp time.Time
	applyCh           chan ApplyMsg

	// state a Raft server must maintain.
	broadcasterCond []*sync.Cond
	applierCond     *sync.Cond

	// server state
	state ServerState

	// presistent state on all servers
	currentTerm int     // latest term server has seen (initialized to 0 on first boot, increases monotonically)
	votedFor    int     // candidateId that received vote in current term (or null if none)
	logs        []Entry // log entries; each entry contains command for state machine, and term when entry was received by leader (first index is 1)

	// volatile state on all servers
	commitIndex int // index of highest log entry known to be committed (initialized to 0, increases monotonically)
	lastApplied int // index of highest log entry applied to state machine (initialized to 0, increases monotonically)

	// volatile state on leaders (reinitialized after election)
	nextIndex  []int // for each server, index of the next log entry to send to that server (initialized to leader last log index + 1)
	matchIndex []int // for each server, index of highest log entry known to be replicated on server (initialized to 0, increases monotonically)

	// snapshot msg
	smsg *ApplyMsg
}

// return currentTerm and whether this server
// believes it is the leader.
func (rf *Raft) GetState() (int, bool) {
	rf.mu.Lock()
	defer rf.mu.Unlock()
	return rf.currentTerm, rf.state == LEADER
}

func (rf *Raft) encodeState() []byte {
	w := new(bytes.Buffer)
	e := labgob.NewEncoder(w)
	e.Encode(rf.currentTerm)
	e.Encode(rf.votedFor)
	e.Encode(rf.logs)
	return w.Bytes()
}

// save Raft's persistent state to stable storage,
// where it can later be retrieved after a crash and restart.
// see paper's Figure 2 for a description of what should be persistent.
// before you've implemented snapshots, you should pass nil as the
// second argument to persister.Save().
// after you've implemented snapshots, pass the current snapshot
// (or nil if there's not yet a snapshot).
func (rf *Raft) persist() {
	if rf.persister.ReadSnapshot() != nil {
		rf.persister.Save(rf.encodeState(), rf.persister.ReadSnapshot())
	} else {
		rf.persister.Save(rf.encodeState(), nil)
	}
}

// restore previously persisted state.
func (rf *Raft) readPersist(data []byte) {
	if data == nil || len(data) < 1 { // bootstrap without any state
		return
	}
	r := bytes.NewBuffer(data)
	d := labgob.NewDecoder(r)
	var currentTerm int
	var votedFor int
	var logs []Entry

	if d.Decode(&currentTerm) != nil || d.Decode(&votedFor) != nil || d.Decode(&logs) != nil {
		log.Fatal("failed to read persist\n")
	} else {
		DPrintf("[%d]: read persist, currentTerm: %d, votedFor: %d, logs: %v\n", rf.me, currentTerm, votedFor, logs)
		rf.currentTerm = currentTerm
		rf.votedFor = votedFor
		rf.logs = logs
		rf.lastApplied = rf.logs[0].Index
		rf.commitIndex = rf.logs[0].Index
	}
}

// the service says it has created a snapshot that has
// all info up to and including index. this means the
// service no longer needs the log through (and including)
// that index. Raft should now trim its log as much as possible.
func (rf *Raft) Snapshot(index int, snapshot []byte) {
	// Your code here (3D).
	rf.mu.Lock()
	defer rf.mu.Unlock()
	// if the snapshot is outdated, just ignore it
	if rf.logs[0].Index >= index {
		return
	}
	firstLogIndex := rf.logs[0].Index
	trimLen := index - firstLogIndex
	// trim the logs
	rf.logs = append([]Entry{}, rf.logs[trimLen:]...)
	rf.logs[0].Command = nil
	rf.persister.Save(rf.encodeState(), snapshot)
}

// the service using Raft (e.g. a k/v server) wants to start
// agreement on the next command to be appended to Raft's log. if this
// server isn't the leader, returns false. otherwise start the
// agreement and return immediately. there is no guarantee that this
// command will ever be committed to the Raft log, since the leader
// may fail or lose an election. even if the Raft instance has been killed,
// this function should return gracefully.
//
// the first return value is the index that the command will appear at
// if it's ever committed. the second return value is the current
// term. the third return value is true if this server believes it is
// the leader.
func (rf *Raft) Start(command interface{}) (int, int, bool) {
	rf.mu.Lock()
	defer rf.mu.Unlock()
	if rf.state != LEADER {
		return -1, -1, false
	}
	defer DPrintf("(Start) [%d]: command %+v, index:%d, term: %d\n", rf.me, command, rf.logs[len(rf.logs)-1].Index, rf.currentTerm)
	rf.logs = append(rf.logs, Entry{
		Term:    rf.currentTerm,
		Index:   rf.logs[len(rf.logs)-1].Index + 1,
		Command: command,
	})
	rf.broadcastAppendEntries(false)
	// Your code here (3B).
	return rf.logs[len(rf.logs)-1].Index, rf.currentTerm, true
}

// Warning: this function is not thread-safe
func (rf *Raft) resetNewTermState(targetTerm int) {
	DPrintf("(ResetTerm)[%d]: received newer term, set term to %d\n", rf.me, targetTerm)
	if rf.currentTerm < targetTerm {
		rf.votedFor = -1
	}
	rf.currentTerm = targetTerm
	rf.state = FOLLOWER // reset to follower
}

// Reply false if term < currentTerm (§5.1)
// If RPC request contains term T > currentTerm:
// set currentTerm = T, convert to follower (§5.1)
func (rf *Raft) checkRequestTerm(args, reply RaftRPC) bool {
	term := args.GetTerm()
	defer reply.SetTerm(rf.currentTerm)
	if term < rf.currentTerm {
		return false
	}
	if term > rf.currentTerm {
		rf.resetNewTermState(term)
	}
	return true
}

// If RPC request or response contains term T > currentTerm:
// set currentTerm = T, convert to follower (§5.1)
func (rf *Raft) checkResponseTerm(args, reply RaftRPC, isElection bool) bool {
	argsTerm := args.GetTerm()
	replyTerm := reply.GetTerm()
	if replyTerm > argsTerm {
		rf.resetNewTermState(replyTerm)
		rf.resetElectionTimer()
		return false
	}
	return isElection || (rf.state == LEADER)
}

// the tester doesn't halt goroutines created by Raft after each test,
// but it does call the Kill() method. your code can use killed() to
// check whether Kill() has been called. the use of atomic avoids the
// need for a lock.
//
// the issue is that long-running goroutines use memory and may chew
// up CPU time, perhaps causing later tests to fail and generating
// confusing debug output. any goroutine with a long-running loop
// should call killed() to check whether it should stop.
func (rf *Raft) Kill() {
	atomic.StoreInt32(&rf.dead, 1)
	// Your code here, if desired.
}

func (rf *Raft) killed() bool {
	z := atomic.LoadInt32(&rf.dead)
	return z == 1
}

// a dedicated applier goroutine to guarantee that each log will be push into applyCh exactly once, ensuring that service's applying entries and raft's committing entries can be parallel
func (rf *Raft) applier() {
	for !rf.killed() {
		rf.mu.Lock()
		// if there is no need to apply entries, just release CPU and wait other goroutine's signal if they commit new entries
		for rf.lastApplied >= rf.commitIndex {
			rf.applierCond.Wait()
		}
		firstLogIndex := rf.logs[0].Index
		commitIndex, lastApplied := rf.commitIndex, rf.lastApplied
		DPrintf("(applier) [%d]: commitIndex: %d, lastApplied: %d, logFirstIndex: %d, logLastIndex: %d\n", rf.me, commitIndex, lastApplied, firstLogIndex, rf.logs[len(rf.logs)-1].Index)
		entries := make([]Entry, commitIndex-lastApplied)
		copy(entries, rf.logs[lastApplied+1-firstLogIndex:commitIndex+1-firstLogIndex])
		if rf.smsg != nil {
			msg := rf.smsg
			rf.smsg = nil
			rf.mu.Unlock()
			rf.applyCh <- *msg
		} else {
			rf.mu.Unlock()
		}
		for _, entry := range entries {
			DPrintf("(applier) [%d]: apply entry %+v\n", rf.me, entry)
			rf.applyCh <- ApplyMsg{
				CommandValid: true,
				Command:      entry.Command,
				CommandTerm:  entry.Term,
				CommandIndex: entry.Index,
			}
		}
		rf.mu.Lock()
		// use commitIndex rather than rf.commitIndex because rf.commitIndex may change during the Unlock() and Lock()
		// use Max(rf.lastApplied, commitIndex) rather than commitIndex directly to avoid concurrently InstallSnapshot rpc causing lastApplied to rollback
		if rf.lastApplied < commitIndex {
			rf.lastApplied = commitIndex
		}
		rf.mu.Unlock()
	}
}

/**
 * Lets illustrate the time line of the ticker function
 * e: election timeout
 * h: heartbeat timeout
 *
 * ---- h ---- h ---- h ---- h ---- h ---- ...
 *
 * First, the server will wake up each fixed heartbeat timeout. This timeout is
 * relatively shorter than the election timeout. If the server is not a leader,
 * it basically do nothing about heartbeat.
 *
 * However, everytime when server wake up, it will check if the election timeout
 * is reached. It might start a new election, if it is not a leader.
 *
 *                      v election timeout found!
 * ---- h1 ---- h2 ---- h3 ---- h ---- h ---- ...
 * --------- e1 ------ e2 ------------ e ---- ...
 *
 * Reseting a new election timeout when the server receives a heartbeat or a
 * vote from another server prevents the election. One shortcomming of the
 * current implementation is that the election timeout does not trigger a new
 * election immediately. It will wait until the next heartbeat timeout.
 */
func (rf *Raft) ticker() {
	for !rf.killed() {
		rf.mu.Lock()
		if rf.state == LEADER {
			rf.broadcastAppendEntries(true)
		} else if rf.isElectionTimeout() {
			rf.startElection()
		}
		rf.mu.Unlock()
		time.Sleep(rf.heartbeatTimeout)
	}
}

// the service or tester wants to create a Raft server. the ports
// of all the Raft servers (including this one) are in peers[]. this
// server's port is peers[me]. all the servers' peers[] arrays
// have the same order. persister is a place for this server to
// save its persistent state, and also initially holds the most
// recent saved state, if any. applyCh is a channel on which the
// tester or service expects Raft to send ApplyMsg messages.
// Make() must return quickly, so it should start goroutines
// for any long-running work.
func Make(peers []*labrpc.ClientEnd, me int,
	persister *Persister, applyCh chan ApplyMsg) *Raft {
	rf := &Raft{}
	rf.peers = peers
	rf.persister = persister
	rf.me = me
	rf.applyCh = applyCh
	rf.heartbeatTimeout = 125 * time.Millisecond
	rf.resetElectionTimer()
	rf.state = FOLLOWER
	rf.votedFor = -1
	rf.logs = make([]Entry, 0)

	// dummy entry to make the index start from 1
	rf.logs = append(rf.logs, Entry{0, 0, nil})

	rf.commitIndex = 0
	rf.lastApplied = 0

	rf.applierCond = sync.NewCond(&rf.mu)
	rf.broadcasterCond = make([]*sync.Cond, len(peers))

	rf.nextIndex = make([]int, len(peers))
	rf.matchIndex = make([]int, len(peers))

	for id := range peers {
		rf.nextIndex[id] = 1
		if id != rf.me {
			rf.broadcasterCond[id] = sync.NewCond(&sync.Mutex{})
			go rf.broadcaster(id)
		}
	}

	rf.smsg = nil

	// initialize from state persisted before a crash
	rf.readPersist(persister.ReadRaftState())

	// start ticker goroutine to start elections
	go rf.ticker()

	go rf.applier()

	return rf
}
