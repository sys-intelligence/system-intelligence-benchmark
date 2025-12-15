#!/bin/bash
set -e

echo '=== Preprocessing 4B Kvraft ==='

cd /workspace

echo 'Copying reference implementations from previous labs...'

echo 'Copying raft implementation...'
mkdir -p src/raft

cat > src/raft/raft.go << 'FILE_EOF_raft_raft_go'
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

FILE_EOF_raft_raft_go

cat > src/raft/election.go << 'FILE_EOF_raft_election_go'
package raft

import (
	"math/rand"
	"sync/atomic"
	"time"
)

// Source: https://pdos.csail.mit.edu/6.824/papers/raft-extended.pdf, Figure 2

type RequestVoteArgs struct {
	BaseRPC          // candidate's term
	CandidateId  int // candidate requesting vote
	LastLogIndex int // index of candidate's last log entry
	LastLogTerm  int // term of candidate's last log entry
}

type RequestVoteReply struct {
	BaseRPC          // currentTerm, for candidate to update itself
	VoteGranted bool // true means candidate received vote
}

// RequestVote RPC handler
// Restart your election timer if you grant a vote to another peer.
func (rf *Raft) RequestVote(args *RequestVoteArgs, reply *RequestVoteReply) {
	rf.mu.Lock()
	defer rf.mu.Unlock()
	defer rf.persist()

	reply.VoteGranted = false

	DPrintf("(RequestVote) [%d]: receive vote request from %d, term %d\n", rf.me, args.CandidateId, args.Term)

	if !rf.checkRequestTerm(args, reply) {
		return
	}

	if (rf.votedFor == -1 || rf.votedFor == args.CandidateId) && rf.isUpToDate(args) {
		reply.VoteGranted = true
		rf.votedFor = args.CandidateId
		rf.resetElectionTimer()
	}
}

func (rf *Raft) isUpToDate(args *RequestVoteArgs) bool {
	lastLog := rf.logs[len(rf.logs)-1]
	candidateIndex := args.LastLogIndex
	candidateTerm := args.LastLogTerm
	return candidateTerm > lastLog.Term || (candidateTerm == lastLog.Term && candidateIndex >= lastLog.Index)
}

func (rf *Raft) sendRequestVote(server int, args *RequestVoteArgs, voteCount *int32) {
	reply := &RequestVoteReply{}
	ok := rf.peers[server].Call("Raft.RequestVote", args, reply)
	if !ok {
		return
	}

	rf.mu.Lock()
	defer rf.mu.Unlock()
	defer rf.persist()

	if !rf.checkResponseTerm(args, reply, true) {
		return
	}

	if !reply.VoteGranted {
		return
	}

	DPrintf("(RequestVote) [%d]: received vote from %d, voteCount: %d\n", rf.me, server, *voteCount)

	// If votes received from majority of servers: become leader
	if atomic.AddInt32(voteCount, 1) > int32(len(rf.peers)/2) &&
		rf.state == CANDIDATE &&
		rf.currentTerm == args.Term {
		rf.state = LEADER
		lastLogIndex := rf.logs[len(rf.logs)-1].Index
		for i := range rf.peers {
			rf.nextIndex[i] = lastLogIndex + 1
			rf.matchIndex[i] = 0
		}
		DPrintf("[%d]: become leader to term %d\n", rf.me, rf.currentTerm)
		// send initial empty AppendEntries RPCs (heartbeat) to each server immediately
		rf.broadcastAppendEntries(true)
	}
	DPrintf("(RequestVote) [%d]: voteCount: %d\n", rf.me, *voteCount)
}

func (rf *Raft) startElection() {
	rf.currentTerm++
	rf.state = CANDIDATE
	rf.votedFor = rf.me
	rf.resetElectionTimer()
	DPrintf("(RequestVote) [%d]: start election, term %d", rf.me, rf.currentTerm)
	lastLog := rf.logs[len(rf.logs)-1]

	voteCount := int32(1)
	args := RequestVoteArgs{
		BaseRPC:      BaseRPC{rf.currentTerm},
		CandidateId:  rf.me,
		LastLogIndex: lastLog.Index,
		LastLogTerm:  lastLog.Term,
	}

	for id := range rf.peers {
		if id == rf.me {
			continue
		}
		go rf.sendRequestVote(id, &args, &voteCount)
	}
}

func (rf *Raft) resetElectionTimer() {
	// election timeout range from 350 to 550
	ms := 350 + (rand.Int63() % 200)
	rf.electionTimeStamp = time.Now()
	rf.electionTimeout = time.Duration(ms) * time.Millisecond
}

func (rf *Raft) isElectionTimeout() bool {
	return time.Now().After(rf.electionTimeStamp.Add(rf.electionTimeout))
}

FILE_EOF_raft_election_go

cat > src/raft/append_entries.go << 'FILE_EOF_raft_append_entries_go'
package raft

// Source: https://pdos.csail.mit.edu/6.824/papers/raft-extended.pdf, Figure 2

type AppendEntriesArgs struct {
	BaseRPC              // leader's term
	LeaderId     int     // so follower can redirect clients
	PrevLogIndex int     // index of log entry immediately preceding new ones
	PrevLogTerm  int     // term of prevLogIndex entry
	Entries      []Entry // log entries to store (empty for heartbeat; may send more than one for efficiency)
	CommitIndex  int     // leader's commitIndex
}

type AppendEntriesReply struct {
	BaseRPC            // currentTerm, for leader to update itself
	Success       bool // true if follower contained entry matching prevLogIndex and prevLogTerm
	ConflictIndex int  // the index of the first conflicting entry
}

// AppendEntries RPC handler
// Reset the election timer if you get an AppendEntries RPC from the current leader
// (i.e., if the term of the AppendEntries arguments is outdated, you should not reset your timer);
func (rf *Raft) AppendEntries(args *AppendEntriesArgs, reply *AppendEntriesReply) {
	rf.mu.Lock()
	defer rf.mu.Unlock()
	defer rf.persist()
	DPrintf("(AppendEntries) [%d] recieve from %d, Term: %d, PrevLogIndex: %d, PrevLogTerm: %d\n", rf.me, args.LeaderId, args.Term, args.PrevLogIndex, args.PrevLogTerm)

	reply.Success = false
	reply.ConflictIndex = -1

	if !rf.checkRequestTerm(args, reply) {
		return
	}

	if rf.state == CANDIDATE {
		rf.state = FOLLOWER
	}

	rf.resetElectionTimer()

	prevLogIndex := args.PrevLogIndex - rf.logs[0].Index

	if prevLogIndex < 0 {
		// force to send a snapshot
		reply.ConflictIndex = 0
		return
	}

	// Reply false if log doesn’t contain an entry at prevLogIndex
	// whose term matches prevLogTerm (§5.3)
	if prevLogIndex >= len(rf.logs) {
		reply.ConflictIndex = rf.logs[len(rf.logs)-1].Index
		return
	}

	// If an existing entry conflicts with a new one (same index
	// but different terms), delete the existing entry and all that
	// follow it (§5.3)
	if rf.logs[prevLogIndex].Term != args.PrevLogTerm {
		// optimization
		curTerm := rf.logs[prevLogIndex].Term
		var conflictIndex int
		for i := prevLogIndex; i > 0; i-- {
			if rf.logs[i-1].Term != curTerm {
				conflictIndex = i
				break
			}
		}
		reply.ConflictIndex = conflictIndex + rf.logs[0].Index
		return
	}
	for idx, entry := range args.Entries {
		logIndex := entry.Index - rf.logs[0].Index
		if logIndex >= len(rf.logs) || rf.logs[logIndex].Term != entry.Term {
			DPrintf("(AppendEntries) [%d] append logs: %v\n", rf.me, args.Entries)
			rf.logs = append([]Entry{}, append(rf.logs[:logIndex], args.Entries[idx:]...)...)
			break
		}
	}
	reply.Success = true
	if args.CommitIndex > rf.commitIndex {
		rf.commitIndex = args.CommitIndex
		if args.CommitIndex-rf.logs[0].Index >= len(rf.logs) {
			rf.commitIndex = rf.logs[len(rf.logs)-1].Index
		}
	}
	rf.applierCond.Signal()
}

func (rf *Raft) sendAppendEntries(server int, args *AppendEntriesArgs) {
	reply := &AppendEntriesReply{}
	ok := rf.peers[server].Call("Raft.AppendEntries", args, reply)
	if !ok {
		return
	}

	DPrintf("(AppendEntries) [%d] recieve reply from %d, Term: %d, Success: %v, ConflictIndex: %d\n", rf.me, server, reply.Term, reply.Success, reply.ConflictIndex)

	rf.mu.Lock()
	defer rf.mu.Unlock()
	defer rf.persist()

	if !rf.checkResponseTerm(args, reply, false) {
		return
	}
	// If successful: update nextIndex and matchIndex for
	// follower (§5.3)
	if reply.Success {
		if len(args.Entries) > 0 {
			rf.nextIndex[server] = args.Entries[len(args.Entries)-1].Index + 1
		}
		rf.matchIndex[server] = rf.nextIndex[server] - 1
		for _, log := range rf.logs {
			index := log.Index
			count := 1
			for peer := range rf.peers {
				if peer != rf.me && rf.matchIndex[peer] >= index {
					count++
				}
			}
			// If there exists an N such that N > commitIndex, a majority
			// of matchIndex[i] ≥ N, and log[N].term == currentTerm:
			// set commitIndex = N (§5.3, §5.4).
			if count > len(rf.peers)/2 && index > rf.commitIndex && log.Term == rf.currentTerm {
				rf.commitIndex = index
			}
		}
	} else {
		if reply.ConflictIndex != -1 {
			rf.nextIndex[server] = reply.ConflictIndex - 1
		} else {
			rf.nextIndex[server] = rf.nextIndex[server] - 1
		}
		if rf.nextIndex[server] < 1 {
			rf.nextIndex[server] = 1
		}
	}
	DPrintf("(AppendEntries) [%d] nextIndex: %v, matchIndex: %v, commitIndex: %d\n", rf.me, rf.nextIndex, rf.matchIndex, rf.commitIndex)
	rf.applierCond.Signal()
}

func (rf *Raft) broadcastAppendEntries(isHeartBeat bool) {
	for peer := range rf.peers {
		if peer != rf.me {
			// if it is a heartbeat we dont care the linearizability of logs append
			if isHeartBeat {
				args := rf.prepareReplicationArgs(peer)
				go rf.sendReplicationRPC(peer, args)
			} else {
				rf.broadcasterCond[peer].Signal()
			}
		}
	}
}

func (rf *Raft) prepareReplicationArgs(peer int) interface{} {
	if rf.nextIndex[peer] > rf.logs[0].Index {
		firstLog := rf.logs[0]
		nextIndex := rf.nextIndex[peer] - firstLog.Index
		prevLog := rf.logs[nextIndex-1]
		logs := make([]Entry, len(rf.logs[nextIndex:]))
		copy(logs, rf.logs[nextIndex:])
		return &AppendEntriesArgs{
			BaseRPC:      BaseRPC{rf.currentTerm},
			LeaderId:     rf.me,
			PrevLogIndex: prevLog.Index,
			PrevLogTerm:  prevLog.Term,
			Entries:      logs,
			CommitIndex:  rf.commitIndex,
		}
	} else {
		return &InstallSnapshotArgs{
			BaseRPC:           BaseRPC{rf.currentTerm},
			LeaderId:          rf.me,
			LastIncludedIndex: rf.logs[0].Index,
			LastIncludedTerm:  rf.logs[0].Term,
			Offset:            0,
			Data:              rf.persister.ReadSnapshot(),
			Done:              true,
		}
	}
}

func (rf *Raft) sendReplicationRPC(peer int, args interface{}) {
	switch v := args.(type) {
	case *AppendEntriesArgs:
		rf.sendAppendEntries(peer, v)
	case *InstallSnapshotArgs:
		rf.sendInstallSnapshot(peer, v)
	default:
		panic("(sendReplicationRPC) SHOULD NOT REACH")
	}
}

func (rf *Raft) isReplicationNeeded(peer int) bool {
	return rf.state == LEADER && rf.matchIndex[peer] < rf.logs[len(rf.logs)-1].Index
}

func (rf *Raft) broadcaster(peer int) {
	rf.broadcasterCond[peer].L.Lock()
	defer rf.broadcasterCond[peer].L.Unlock()
	for !rf.killed() {
		rf.mu.Lock()
		for !rf.isReplicationNeeded(peer) {
			rf.mu.Unlock()
			rf.broadcasterCond[peer].Wait()
			rf.mu.Lock()
		}
		args := rf.prepareReplicationArgs(peer)
		rf.mu.Unlock()
		rf.sendReplicationRPC(peer, args)
	}
}

FILE_EOF_raft_append_entries_go

cat > src/raft/install_snapshot.go << 'FILE_EOF_raft_install_snapshot_go'
package raft

type InstallSnapshotArgs struct {
	BaseRPC
	LeaderId          int
	LastIncludedIndex int
	LastIncludedTerm  int
	Offset            int
	Data              []byte
	Done              bool
}

type InstallSnapshotReply struct {
	BaseRPC
}

// InstallSnapshot RPC handler
func (rf *Raft) InstallSnapshot(args *InstallSnapshotArgs, reply *InstallSnapshotReply) {
	rf.mu.Lock()
	defer rf.mu.Unlock()

	if !rf.checkRequestTerm(args, reply) {
		return
	}

	if args.LastIncludedIndex <= rf.commitIndex {
		return
	}
	prevCommitIndex := rf.commitIndex
	prevLastApplied := rf.lastApplied
	defer DPrintf("(InstallSnapshot) [%d]: LastIncludedIndex: %d, LastIncludedTerm: %d, prevCommitIndex: %d, prevLastApplied: %d\n", rf.me, args.LastIncludedIndex, args.LastIncludedTerm, prevCommitIndex, prevLastApplied)
	rf.resetElectionTimer()

	rf.commitIndex = args.LastIncludedIndex
	rf.lastApplied = args.LastIncludedIndex
	// 2. Create new snapshot file if first chunk (offset is 0)
	// 3. Write data into snapshot file at given offset
	// 4. Reply and wait for more data chunks if done is false
	if !args.Done {
		return
	}
	// 5. Save snapshot file, discard any existing or partial snapshot with a
	//    smaller index
	// 6. If existing log entry has same index and term as snapshot’s last
	//    included entry, retain log entries following it and reply
	// 7. Discard the entire log
	// 8. Reset state machine using snapshot contents (and load snapshot’s
	//    cluster configuration)
	firstLogIndex := rf.logs[0].Index
	if firstLogIndex <= args.LastIncludedIndex {
		rf.logs = append([]Entry{}, Entry{
			Index:   args.LastIncludedIndex,
			Term:    args.LastIncludedTerm,
			Command: nil,
		})
	} else if firstLogIndex < args.LastIncludedIndex {
		trimLen := args.LastIncludedIndex - firstLogIndex
		rf.logs = append([]Entry{}, rf.logs[trimLen:]...)
		rf.logs[0].Command = nil
	}
	rf.persister.Save(rf.encodeState(), args.Data)
	rf.smsg = &ApplyMsg{
		SnapshotValid: true,
		Snapshot:      args.Data,
		SnapshotTerm:  args.LastIncludedTerm,
		SnapshotIndex: args.LastIncludedIndex,
	}
}

func (rf *Raft) sendInstallSnapshot(server int, args *InstallSnapshotArgs) {
	reply := &InstallSnapshotReply{}
	ok := rf.peers[server].Call("Raft.InstallSnapshot", args, reply)
	if !ok {
		return
	}

	rf.mu.Lock()
	defer rf.mu.Unlock()

	if !rf.checkResponseTerm(args, reply, false) {
		return
	}

	if args.LastIncludedIndex != rf.logs[0].Index {
		return
	}

	rf.nextIndex[server] = args.LastIncludedIndex + 1
	rf.matchIndex[server] = args.LastIncludedIndex

	rf.persister.Save(rf.encodeState(), args.Data)
}

FILE_EOF_raft_install_snapshot_go

cat > src/raft/util.go << 'FILE_EOF_raft_util_go'
package raft

import (
	"log"
	"os"
)

// Debugging
var Debug = os.Getenv("DEBUG") == "1"

func DPrintf(format string, a ...interface{}) {
	if !Debug {
		return
	}
	log.Printf(format, a...)
}

FILE_EOF_raft_util_go

echo 'Copying kvsrv implementation...'
mkdir -p src/kvsrv

cat > src/kvsrv/client.go << 'FILE_EOF_kvsrv_client_go'
package kvsrv

import (
	"crypto/rand"
	"math/big"

	"6.5840/labrpc"
)

type Clerk struct {
	server   *labrpc.ClientEnd
	clientId int64
	seqNum   int
}

func nrand() int64 {
	max := big.NewInt(int64(1) << 62)
	bigx, _ := rand.Int(rand.Reader, max)
	x := bigx.Int64()
	return x
}

func MakeClerk(server *labrpc.ClientEnd) *Clerk {
	ck := new(Clerk)
	ck.server = server
	ck.clientId = nrand()
	ck.seqNum = 0
	return ck
}

// fetch the current value for a key.
// returns "" if the key does not exist.
// keeps trying forever in the face of all other errors.
//
// you can send an RPC with code like this:
// ok := ck.server.Call("KVServer.Get", &args, &reply)
//
// the types of args and reply (including whether they are pointers)
// must match the declared types of the RPC handler function's
// arguments. and reply must be passed as a pointer.
func (ck *Clerk) Get(key string) string {
	ck.seqNum++
	args := GetArgs{
		Key:      key,
		ClientId: ck.clientId,
		SeqNum:   ck.seqNum,
	}
	reply := GetReply{}
	for !ck.server.Call("KVServer.Get", &args, &reply) {
	}
	return reply.Value
}

// shared by Put and Append.
//
// you can send an RPC with code like this:
// ok := ck.server.Call("KVServer."+op, &args, &reply)
//
// the types of args and reply (including whether they are pointers)
// must match the declared types of the RPC handler function's
// arguments. and reply must be passed as a pointer.
func (ck *Clerk) PutAppend(key string, value string, op string) string {
	ck.seqNum++
	args := PutAppendArgs{
		Key:      key,
		Value:    value,
		ClientId: ck.clientId,
		SeqNum:   ck.seqNum,
	}
	reply := PutAppendReply{}
	for !ck.server.Call("KVServer."+op, &args, &reply) {
	}
	return reply.Value
}

func (ck *Clerk) Put(key string, value string) {
	ck.PutAppend(key, value, "Put")
}

// Append value to key's value and return that value
func (ck *Clerk) Append(key string, value string) string {
	return ck.PutAppend(key, value, "Append")
}

FILE_EOF_kvsrv_client_go

cat > src/kvsrv/common.go << 'FILE_EOF_kvsrv_common_go'
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

FILE_EOF_kvsrv_common_go

cat > src/kvsrv/server.go << 'FILE_EOF_kvsrv_server_go'
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

FILE_EOF_kvsrv_server_go

echo 'Copying mr implementation...'
mkdir -p src/mr

cat > src/mr/coordinator.go << 'FILE_EOF_mr_coordinator_go'
package mr

import (
	"log"
	"math"
	"net"
	"net/http"
	"net/rpc"
	"os"
	"sync"
	"time"
)

const SUCCESS = math.MaxInt32

type Coordinator struct {
	// Your definitions here.
	tasks   chan Work // a taskqueue
	mu      sync.Mutex
	terms   []int
	wg      sync.WaitGroup
	nMap    int
	nReduce int
	done    bool
}

func (c *Coordinator) CallGetWork(args *WorkArgs, reply *WorkReply) error {
	if len(c.tasks) == 0 {
		reply.HasWork = false
		return nil
	}
	reply.Work = <-c.tasks
	c.mu.Lock()
	reply.Term = c.terms[reply.Work.FileIndex]
	c.mu.Unlock()
	reply.HasWork = true

	go func() {
		time.Sleep(10 * time.Second)
		c.mu.Lock()
		defer c.mu.Unlock()
		if c.terms[reply.Work.FileIndex] == SUCCESS {
			return
		}
		c.terms[reply.Work.FileIndex]++
		c.tasks <- reply.Work
	}()

	return nil
}

func (c *Coordinator) CallReport(args *ReportArgs, reply *ReportReply) error {
	c.mu.Lock()
	defer c.mu.Unlock()

	if c.terms[args.Work.FileIndex] != args.Term {
		reply.Success = false
		return nil
	}
	c.terms[args.Work.FileIndex] = SUCCESS
	c.wg.Done()
	reply.Success = true
	return nil
}

// start a thread that listens for RPCs from worker.go
func (c *Coordinator) server() {
	rpc.Register(c)
	rpc.HandleHTTP()
	//l, e := net.Listen("tcp", ":1234")
	sockname := coordinatorSock()
	os.Remove(sockname)
	l, e := net.Listen("unix", sockname)
	if e != nil {
		log.Fatal("listen error:", e)
	}
	go http.Serve(l, nil)
}

// main/mrcoordinator.go calls Done() periodically to find out
// if the entire job has finished.
func (c *Coordinator) Done() bool {
	return c.done
}

func StartReduceWork(c *Coordinator) {
	c.wg.Wait()
	c.terms = make([]int, c.nReduce)
	for i := 0; i < c.nReduce; i++ {
		c.tasks <- Work{
			WorkType:  REDUCE,
			FileIndex: i,
			NReduce:   c.nReduce,
			NMapWork:  c.nMap,
		}
		c.wg.Add(1)
	}
	go WorkDone(c)
}

func WorkDone(c *Coordinator) {
	c.wg.Wait()
	c.done = true
}

// create a Coordinator.
// main/mrcoordinator.go calls this function.
// nReduce is the number of reduce tasks to use.
func MakeCoordinator(files []string, nReduce int) *Coordinator {

	var buflen int
	if len(files) > nReduce {
		buflen = len(files)
	} else {
		buflen = nReduce
	}

	c := Coordinator{
		nMap:    len(files),
		nReduce: nReduce,
		wg:      sync.WaitGroup{},
		tasks:   make(chan Work, buflen),
		terms:   make([]int, len(files)),
		done:    false,
	}

	for idx, file := range files {
		c.tasks <- Work{
			WorkType:  MAP,
			Filename:  file,
			FileIndex: idx,
			NReduce:   c.nReduce,
			NMapWork:  c.nMap,
		}
		c.wg.Add(1)
	}
	go StartReduceWork(&c)
	c.server()

	return &c
}

FILE_EOF_mr_coordinator_go

cat > src/mr/rpc.go << 'FILE_EOF_mr_rpc_go'
package mr

//
// RPC definitions.
//
// remember to capitalize all names.
//

import (
	"os"
	"strconv"
)

//
// example to show how to declare the arguments
// and reply for an RPC.
//

type ExampleArgs struct {
	X int
}

type ExampleReply struct {
	Y int
}

/*-Define Work-*/

type WorkStatus int

const (
	IDLE WorkStatus = iota
	START
	FINISH
)

type WorkType int

const (
	MAP WorkType = iota
	REDUCE
)

type Work struct {
	WorkType  WorkType // MAP or REDUCE
	Filename  string
	FileIndex int // This is a convention for mr-X index
	NMapWork  int // how many map files
	NReduce   int // how many reduce files
}

type WorkArgs struct {
	WorkerID int
}

type WorkReply struct {
	HasWork bool
	Work    Work
	Term    int
}

/*-Define Report-*/
// Report work finish only if success
type ReportArgs struct {
	Work Work
	Term int
}

type ReportReply struct {
	Success bool
}

// Cook up a unique-ish UNIX-domain socket name
// in /var/tmp, for the coordinator.
// Can't use the current directory since
// Athena AFS doesn't support UNIX-domain sockets.
func coordinatorSock() string {
	s := "/var/tmp/5840-mr-"
	s += strconv.Itoa(os.Getuid())
	return s
}

FILE_EOF_mr_rpc_go

cat > src/mr/worker.go << 'FILE_EOF_mr_worker_go'
package mr

import (
	"encoding/json"
	"fmt"
	"hash/fnv"
	"io/ioutil"
	"log"
	"net/rpc"
	"os"
	"sort"
	"time"
)

// for sorting by key.
type ByKey []KeyValue

// for sorting by key.
func (a ByKey) Len() int           { return len(a) }
func (a ByKey) Swap(i, j int)      { a[i], a[j] = a[j], a[i] }
func (a ByKey) Less(i, j int) bool { return a[i].Key < a[j].Key }

// Map functions return a slice of KeyValue.
type KeyValue struct {
	Key   string
	Value string
}

// use ihash(key) % NReduce to choose the reduce
// task number for each KeyValue emitted by Map.
func ihash(key string) int {
	h := fnv.New32a()
	h.Write([]byte(key))
	return int(h.Sum32() & 0x7fffffff)
}

// main/mrworker.go calls this function.
func Worker(mapf func(string, string) []KeyValue,
	reducef func(string, []string) string) {

	// Your worker implementation here.
	for {
		r := CallGetWok()
		if !r.HasWork {
			time.Sleep(3 * time.Second)
			continue
		}

		switch r.Work.WorkType {
		case MAP:
			DoMapWork(r.Work, mapf, r.Term)
		case REDUCE:
			DoReduceWork(r.Work, reducef, r.Term)
		}
	}
}

func DoReduceWork(work Work, reducef func(string, []string) string, term int) {
	fileIndex := work.FileIndex
	intermediate := []KeyValue{}

	for i := 0; i < work.NMapWork; i++ {
		filename := fmt.Sprintf("mr-%d-%d", i, fileIndex)
		file, err := os.Open(filename)

		if err != nil {
			log.Fatalf("cannot open %v", filename)
		}

		dec := json.NewDecoder(file)

		for {
			var kv KeyValue
			if err := dec.Decode(&kv); err != nil {
				break
			}
			intermediate = append(intermediate, kv)
		}
		file.Close()
	}

	sort.Sort(ByKey(intermediate))

	oname := fmt.Sprintf("mr-out-%d", fileIndex)
	ofile, _ := ioutil.TempFile(".", oname)

	//
	// call Reduce on each distinct key in intermediate[],
	// and print the result to mr-out-0.
	//
	i := 0
	for i < len(intermediate) {
		j := i + 1
		for j < len(intermediate) && intermediate[j].Key == intermediate[i].Key {
			j++
		}
		values := []string{}
		for k := i; k < j; k++ {
			values = append(values, intermediate[k].Value)
		}
		output := reducef(intermediate[i].Key, values)

		// this is the correct format for each line of Reduce output.
		fmt.Fprintf(ofile, "%v %v\n", intermediate[i].Key, output)

		i = j
	}

	os.Rename(ofile.Name(), oname)

	CallReport(work, term)
}

func DoMapWork(work Work, mapf func(string, string) []KeyValue, term int) {
	filename := work.Filename

	file, err := os.Open(filename)
	if err != nil {
		log.Fatalf("cannot open %v", filename)
	}

	content, err := ioutil.ReadAll(file)

	if err != nil {
		log.Fatalf("cannot read %v", filename)
	}

	file.Close()

	kva := mapf(work.Filename, string(content))

	//make a
	for i := 0; i < work.NReduce; i++ {
		imtFilename := fmt.Sprintf("mr-%d-%d", work.FileIndex, i)

		imtFile, err := ioutil.TempFile(".", imtFilename)

		enc := json.NewEncoder(imtFile)

		if err != nil {
			log.Fatalf("cannot create %v", imtFilename)
		}

		for _, kv := range kva {
			hash := ihash(kv.Key) % work.NReduce
			if hash == i {
				err := enc.Encode(&kv)
				if err != nil {
					log.Fatalf("cannot encode %v", kv)
				}
			}
		}

		imtFile.Close()

		os.Rename(imtFile.Name(), imtFilename)
	}

	CallReport(work, term)
}

func CallReport(w Work, term int) {
	args := ReportArgs{
		Work: w,
		Term: term,
	}
	reply := ReportReply{}
	ok := call("Coordinator.CallReport", &args, &reply)

	if !ok {
		fmt.Printf("call failed!\n")
	}
}

func CallGetWok() WorkReply {
	args := WorkArgs{}
	reply := WorkReply{}
	ok := call("Coordinator.CallGetWork", &args, &reply)

	if !ok {
		fmt.Printf("call failed!\n")
	}

	return reply
}

// example function to show how to make an RPC call to the coordinator.
//
// the RPC argument and reply types are defined in rpc.go.
func CallExample() {

	// declare an argument structure.
	args := ExampleArgs{}

	// fill in the argument(s).
	args.X = 99

	// declare a reply structure.
	reply := ExampleReply{}

	// send the RPC request, wait for the reply.
	// the "Coordinator.Example" tells the
	// receiving server that we'd like to call
	// the Example() method of struct Coordinator.
	ok := call("Coordinator.Example", &args, &reply)
	if ok {
		// reply.Y should be 100.
		fmt.Printf("reply.Y %v\n", reply.Y)
	} else {
		fmt.Printf("call failed!\n")
	}
}

// send an RPC request to the coordinator, wait for the response.
// usually returns true.
// returns false if something goes wrong.
func call(rpcname string, args interface{}, reply interface{}) bool {
	// c, err := rpc.DialHTTP("tcp", "127.0.0.1"+":1234")
	sockname := coordinatorSock()
	c, err := rpc.DialHTTP("unix", sockname)
	if err != nil {
		log.Fatal("dialing:", err)
	}
	defer c.Close()

	err = c.Call(rpcname, args, reply)
	if err == nil {
		return true
	}

	fmt.Println(err)
	return false
}

FILE_EOF_mr_worker_go


echo 'Creating checksums for protected files...'
PROTECTED_FILES=(
    "src/kvraft/config.go"
    "src/kvraft/test_test.go"
)

mkdir -p /tmp/checksums
for file in "${PROTECTED_FILES[@]}"; do
    if [ -f "$file" ]; then
        sha256sum "$file" > "/tmp/checksums/$(basename $file).$(dirname $file | tr '/' '_').sha256"
        echo "  $file"
    fi
done

echo ''
echo 'Preprocessing complete'
echo 'Agent should focus on implementing:'
echo '  - src/kvraft/client.go'
echo '  - src/kvraft/common.go'
echo '  - src/kvraft/server.go'

exit 0