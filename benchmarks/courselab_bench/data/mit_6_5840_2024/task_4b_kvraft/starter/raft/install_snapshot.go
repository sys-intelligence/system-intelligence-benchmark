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
