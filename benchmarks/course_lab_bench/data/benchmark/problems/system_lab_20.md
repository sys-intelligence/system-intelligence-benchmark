# Problem Context

## Introduction

This is the first in a series of labs in which you'll build a fault-tolerant key/value storage system. In this lab you'll implement Raft, a replicated state machine protocol. In the next lab you'll build a key/value service on top of Raft. Then you will ÂshardÂ your service over multiple replicated state machines for higher performance.

A replicated service achieves fault tolerance by storing complete copies of its state (i.e., data) on multiple replica servers. Replication allows the service to continue operating even if some of its servers experience failures (crashes or a broken or flaky network). The challenge is that failures may cause the replicas to hold differing copies of the data.

Raft organizes client requests into a sequence, called the log, and ensures that all the replica servers see the same log. Each replica executes client requests in log order, applying them to its local copy of the service's state. Since all the live replicas see the same log contents, they all execute the same requests in the same order, and thus continue to have identical service state. If a server fails but later recovers, Raft takes care of bringing its log up to date. Raft will continue to operate as long as at least a majority of the servers are alive and can talk to each other. If there is no such majority, Raft will make no progress, but will pick up where it left off as soon as a majority can communicate again.

In this lab you'll implement Raft as a Go object type with associated methods, meant to be used as a module in a larger service. A set of Raft instances talk to each other with RPC to maintain replicated logs. Your Raft interface will support an indefinite sequence of numbered commands, also called log entries. The entries are numbered with *index numbers*. The log entry with a given index will eventually be committed. At that point, your Raft should send the log entry to the larger service for it to execute.

You should follow the design in the [extended Raft paper](http://nil.csail.mit.edu/6.5840/2025/papers/raft-extended.pdf), with particular attention to Figure 2. You'll implement most of what's in the paper, including saving persistent state and reading it after a node fails and then restarts. You will not implement cluster membership changes (Section 6).

This lab is due in four parts. You must submit each part on the corresponding due date.

## Getiting Started

Do a `git pull` to get the latest lab software.

If you have done Lab 1, you already have a copy of the lab source code. If not, you can find directions for obtaining the source via git in the [Lab 1 instructions](http://nil.csail.mit.edu/6.5840/2025/labs/lab-mr.html).

We supply you with skeleton code `src/raft/raft.go`. We also supply a set of tests, which you should use to drive your implementation efforts, and which we'll use to grade your submitted lab. The tests are in `src/raft/raft_test.go`.

When we grade your submissions, we will run the tests without the [`-race` flag](https://go.dev/blog/race-detector). However, you should check that your code does not have races, by running the tests with the `-race` flag as you develop your solution.

To get up and running, execute the following commands. Don't forget the `git pull` to get the latest software.

```
$ cd ~/6.5840
$ git pull
...
$ cd src/raft1
$ go test
Test (3A): initial election (reliable network)...
Fatal: expected one leader, got none
--- FAIL: TestInitialElection3A (4.90s)
Test (3A): election after network failure (reliable network)...
Fatal: expected one leader, got none
--- FAIL: TestReElection3A (5.05s)
...
$
```

## The Code

Implement Raft by adding code to `raft/raft.go`. In that file you'll find skeleton code, plus examples of how to send and receive RPCs.

Your implementation must support the following interface, which the tester and (eventually) your key/value server will use. You'll find more details in comments in `raft.go`.

```
// create a new Raft server instance:
rf := Make(peers, me, persister, applyCh)

// start agreement on a new log entry:
rf.Start(command interface{}) (index, term, isleader)

// ask a Raft for its current term, and whether it thinks it is leader
rf.GetState() (term, isLeader)

// each time a new entry is committed to the log, each Raft peer
// should send an ApplyMsg to the service (or tester).
type ApplyMsg
```

A service calls `Make(peers,me,Â)` to create a Raft peer. The peers argument is an array of network identifiers of the Raft peers (including this one), for use with RPC. The `me` argument is the index of this peer in the peers array. `Start(command)` asks Raft to start the processing to append the command to the replicated log. `Start()` should return immediately, without waiting for the log appends to complete. The service expects your implementation to send an `ApplyMsg` for each newly committed log entry to the `applyCh` channel argument to `Make()`.

`raft.go` contains example code that sends an RPC (`sendRequestVote()`) and that handles an incoming RPC (`RequestVote()`). Your Raft peers should exchange RPCs using the labrpc Go package (source in `src/labrpc`). The tester can tell `labrpc` to delay RPCs, re-order them, and discard them to simulate various network failures. While you can temporarily modify `labrpc`, make sure your Raft works with the original `labrpc`, since that's what we'll use to test and grade your lab. Your Raft instances must interact only with RPC; for example, they are not allowed to communicate using shared Go variables or files.

Subsequent labs build on this lab, so it is important to give yourself enough time to write solid code.

# Your Task

As things stand now, a rebooting server replays the complete Raft log in order to restore its state. However, it's not practical for a long-running service to remember the complete Raft log forever. Instead, you'll modify Raft to cooperate with services that persistently store a "snapshot" of their state from time to time, at which point Raft discards log entries that precede the snapshot. The result is a smaller amount of persistent data and faster restart. However, it's now possible for a follower to fall so far behind that the leader has discarded the log entries it needs to catch up; the leader must then send a snapshot plus the log starting at the time of the snapshot. Section 7 of the [extended Raft paper](http://nil.csail.mit.edu/6.5840/2025/papers/raft-extended.pdf) outlines the scheme; you will have to design the details.

Your Raft must provide the following function that the service can call with a serialized snapshot of its state:

```
Snapshot(index int, snapshot []byte)
```

In Lab 3D, the tester calls `Snapshot()` periodically. In Lab 4, you will write a key/value server that calls `Snapshot()`; the snapshot will contain the complete table of key/value pairs. The service layer calls `Snapshot()` on every peer (not just on the leader).

The `index` argument indicates the highest log entry that's reflected in the snapshot. Raft should discard its log entries before that point. You'll need to revise your Raft code to operate while storing only the tail of the log.

You'll need to implement the `InstallSnapshot` RPC discussed in the paper that allows a Raft leader to tell a lagging Raft peer to replace its state with a snapshot. You will likely need to think through how InstallSnapshot should interact with the state and rules in Figure 2.

When a follower's Raft code receives an InstallSnapshot RPC, it can use the `applyCh` to send the snapshot to the service in an `ApplyMsg`. The `ApplyMsg` struct definition already contains the fields you will need (and which the tester expects). Take care that these snapshots only advance the service's state, and don't cause it to move backwards.

If a server crashes, it must restart from persisted data. Your Raft should persist both Raft state and the corresponding snapshot. Use the second argument to `persister.Save()` to save the snapshot. If there's no snapshot, pass `nil` as the second argument.

When a server restarts, the application layer reads the persisted snapshot and restores its saved state.

Implement `Snapshot()` and the InstallSnapshot RPC, as well as the changes to Raft to support these (e.g, operation with a trimmed log). Your solution is complete when it passes the 3D tests (and all the previous Lab 3 tests).

- `git pull` to make sure you have the latest software.
- A good place to start is to modify your code to so that it is able to store just the part of the log starting at some index X. Initially you can set X to zero and run the 3B/3C tests. Then make `Snapshot(index)` discard the log before `index`, and set X equal to `index`. If all goes well you should now pass the first 3D test.
- A common reason for failing the first 3D test is that followers take too long to catch up to the leader.
- Next: have the leader send an InstallSnapshot RPC if it doesn't have the log entries required to bring a follower up to date.
- Send the entire snapshot in a single InstallSnapshot RPC. Don't implement Figure 13's `offset` mechanism for splitting up the snapshot.
- Raft must discard old log entries in a way that allows the Go garbage collector to free and re-use the memory; this requires that there be no reachable references (pointers) to the discarded log entries.
- A reasonable amount of time to consume for the full set of Lab 3 tests (3A+3B+3C+3D) without `-race` is 6 minutes of real time and one minute of CPU time. When running with `-race`, it is about 10 minutes of real time and two minutes of CPU time.

Your code should pass all the 3D tests (as shown below), as well as the 3A, 3B, and 3C tests.

```
$ go test -run 3D
Test (3D): snapshots basic (reliable network)...
  ... Passed --   3.3  3   522    0
Test (3D): install snapshots (disconnect) (reliable network)...
  ... Passed --  48.4  3  2710    0
Test (3D): install snapshots (disconnect) (unreliable network)...
  ... Passed --  56.1  3  3025    0
Test (3D): install snapshots (crash) (reliable network)...
  ... Passed --  33.3  3  1559    0
Test (3D): install snapshots (crash) (unreliable network)...
  ... Passed --  38.1  3  1723    0
Test (3D): crash and restart all servers (unreliable network)...
  ... Passed --  11.2  3   296    0
Test (3D): snapshot initialization after crash (unreliable network)...
  ... Passed --   4.3  3    84    0
PASS
ok      6.5840/raft1    195.006s
```
