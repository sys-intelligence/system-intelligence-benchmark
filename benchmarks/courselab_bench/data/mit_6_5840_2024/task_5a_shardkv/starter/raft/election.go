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
