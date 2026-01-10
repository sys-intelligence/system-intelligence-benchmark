# Raft

### Introduction

This is the first in a series of labs in which you'll build a fault-tolerant key/value storage system. In this lab you'll implement Raft, a replicated state machine protocol. In the next lab you'll build a key/value service on top of Raft. Then you will "shard" your service over multiple replicated state machines for higher performance.

A replicated service achieves fault tolerance by storing complete copies of its state (i.e., data) on multiple replica servers. Replication allows the service to continue operating even if some of its servers experience failures (crashes or a broken or flaky network). The challenge is that failures may cause the replicas to hold differing copies of the data.

Raft organizes client requests into a sequence, called the log, and ensures that all the replica servers see the same log. Each replica executes client requests in log order, applying them to its local copy of the service's state. Since all the live replicas see the same log contents, they all execute the same requests in the same order, and thus continue to have identical service state. If a server fails but later recovers, Raft takes care of bringing its log up to date. Raft will continue to operate as long as at least a majority of the servers are alive and can talk to each other. If there is no such majority, Raft will make no progress, but will pick up where it left off as soon as a majority can communicate again.

In this lab you'll implement Raft as a Go object type with associated methods, meant to be used as a module in a larger service. A set of Raft instances talk to each other with RPC to maintain replicated logs. Your Raft interface will support an indefinite sequence of numbered commands, also called log entries. The entries are numbered with _index numbers_. The log entry with a given index will eventually be committed. At that point, your Raft should send the log entry to the larger service for it to execute.

You should follow the design in the extended Raft paper, with particular attention to Figure 2. You'll implement most of what's in the paper, including saving persistent state and reading it after a node fails and then restarts. You will not implement cluster membership changes (Section 6).

This lab is due in four parts. You must submit each part on the corresponding due date.

### Getting Started

We supply you with skeleton code `src/raft/raft.go`. We also supply a set of tests, which you should use to drive your implementation efforts, and which we'll use to grade your submitted lab. The tests are in `src/raft/test_test.go`.

When we grade your submissions, we will run the tests without the `-race` flag. However, you should check that your code does not have races, by running the tests with the `-race` flag as you develop your solution.

To get up and running, execute the following commands:

```sh
$ cd src/raft
$ go test
Test (3A): initial election ...
--- FAIL: TestInitialElection3A (5.04s)
config.go:326: expected one leader, got none
Test (3A): election after network failure ...
--- FAIL: TestReElection3A (5.03s)
config.go:326: expected one leader, got none
...
$
```

### The code

Implement Raft by adding code to `raft/raft.go`. In that file you'll find skeleton code, plus examples of how to send and receive RPCs.

Your implementation must support the following interface, which the tester and (eventually) your key/value server will use. You'll find more details in comments in `raft.go`.

```go
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

A service calls `Make(peers,me,…)` to create a Raft peer. The peers argument is an array of network identifiers of the Raft peers (including this one), for use with RPC. The `me` argument is the index of this peer in the peers array. `Start(command)` asks Raft to start the processing to append the command to the replicated log. `Start()` should return immediately, without waiting for the log appends to complete. The service expects your implementation to send an `ApplyMsg` for each newly committed log entry to the `applyCh` channel argument to `Make()`.

`raft.go` contains example code that sends an RPC (`sendRequestVote()`) and that handles an incoming RPC (`RequestVote()`). Your Raft peers should exchange RPCs using the labrpc Go package (source in `src/labrpc`). The tester can tell `labrpc` to delay RPCs, re-order them, and discard them to simulate various network failures. While you can temporarily modify `labrpc`, make sure your Raft works with the original `labrpc`, since that's what we'll use to test and grade your lab. Your Raft instances must interact only with RPC; for example, they are not allowed to communicate using shared Go variables or files.

Subsequent labs build on this lab, so it is important to give yourself enough time to write solid code.

### Part 3A: leader election ("moderate")

#### Task

Implement Raft leader election and heartbeats (`AppendEntries` RPCs with no log entries). The goal for Part 3A is for a single leader to be elected, for the leader to remain the leader if there are no failures, and for a new leader to take over if the old leader fails or if packets to/from the old leader are lost. Run `go test -run 3A` to test your 3A code.

#### Hints

- You can't easily run your Raft implementation directly; instead you should run it by way of the tester, i.e. `go test -run 3A` .
- Follow the paper's Figure 2. At this point you care about sending and receiving RequestVote RPCs, the Rules for Servers that relate to elections, and the State related to leader election,
- Add the Figure 2 state for leader election to the `Raft` struct in `raft.go`. You'll also need to define a struct to hold information about each log entry.
- Fill in the `RequestVoteArgs` and `RequestVoteReply` structs. Modify `Make()` to create a background goroutine that will kick off leader election periodically by sending out `RequestVote` RPCs when it hasn't heard from another peer for a while. Implement the `RequestVote()` RPC handler so that servers will vote for one another.
- To implement heartbeats, define an `AppendEntries` RPC struct (though you may not need all the arguments yet), and have the leader send them out periodically. Write an `AppendEntries` RPC handler method.
- The tester requires that the leader send heartbeat RPCs no more than ten times per second.
- The tester requires your Raft to elect a new leader within five seconds of the failure of the old leader (if a majority of peers can still communicate).
- The paper's Section 5.2 mentions election timeouts in the range of 150 to 300 milliseconds. Such a range only makes sense if the leader sends heartbeats considerably more often than once per 150 milliseconds (e.g., once per 10 milliseconds). Because the tester limits you tens of heartbeats per second, you will have to use an election timeout larger than the paper's 150 to 300 milliseconds, but not too large, because then you may fail to elect a leader within five seconds.
- You may find Go's rand useful.
- You'll need to write code that takes actions periodically or after delays in time. The easiest way to do this is to create a goroutine with a loop that calls time.Sleep(); see the ticker() goroutine that Make() creates for this purpose. Don't use Go's `time.Timer` or `time.Ticker`, which are difficult to use correctly.
- If your code has trouble passing the tests, read the paper's Figure 2 again; the full logic for leader election is spread over multiple parts of the figure.
- Don't forget to implement `GetState()`.
- The tester calls your Raft's `rf.Kill()` when it is permanently shutting down an instance. You can check whether `Kill()` has been called using `rf.killed()`. You may want to do this in all loops, to avoid having dead Raft instances print confusing messages.
- Go RPC sends only struct fields whose names start with capital letters. Sub-structures must also have capitalized field names (e.g. fields of log records in an array). The `labgob` package will warn you about this; don't ignore the warnings.
- The most challenging part of this lab may be the debugging. Spend some time making your implementation easy to debug.

Be sure you pass the 3A tests before submitting Part 3A, so that you see something like this:

```sh
$ go test -run 3A
Test (3A): initial election ...
... Passed -- 3.5 3 58 16840 0
Test (3A): election after network failure ...
... Passed -- 5.4 3 118 25269 0
Test (3A): multiple elections ...
... Passed -- 7.3 7 624 138014 0
PASS
ok raft 16.265s
$
```

Each "Passed" line contains five numbers; these are the time that the test took in seconds, the number of Raft peers, the number of RPCs sent during the test, the total number of bytes in the RPC messages, and the number of log entries that Raft reports were committed. Your numbers will differ from those shown here. You can ignore the numbers if you like, but they may help you sanity-check the number of RPCs that your implementation sends. For all of labs 3, 4, and 5, the grading script will fail your solution if it takes more than 600 seconds for all of the tests (`go test`), or if any individual test takes more than 120 seconds.

When we grade your submissions, we will run the tests without the `-race` flag. However, you should make sure that your code consistently passes the tests with the `-race` flag.

### Part 3B: log ("hard")

#### Task

Implement the leader and follower code to append new log entries, so that the `go test -run 3B` tests pass.

#### Hints

- Your first goal should be to pass `TestBasicAgree3B()`. Start by implementing `Start()`, then write the code to send and receive new log entries via `AppendEntries` RPCs, following Figure 2. Send each newly committed entry on `applyCh` on each peer.
- You will need to implement the election restriction (section 5.4.1 in the paper).
- Your code may have loops that repeatedly check for certain events. Don't have these loops execute continuously without pausing, since that will slow your implementation enough that it fails tests. Use Go's condition variables, or insert a `time.Sleep(10 * time.Millisecond)` in each loop iteration.
- Do yourself a favor for future labs and write (or re-write) code that's clean and clear.
- If you fail a test, look at `test_test.go` and `config.go` to understand what's being tested. `config.go` also illustrates how the tester uses the Raft API.

The tests for upcoming labs may fail your code if it runs too slowly. You can check how much real time and CPU time your solution uses with the time command. Here's typical output:

```sh
$ time go test -run 3B
Test (3B): basic agreement ...
... Passed -- 0.9 3 16 4572 3
Test (3B): RPC byte count ...
... Passed -- 1.7 3 48 114536 11
Test (3B): agreement after follower reconnects ...
... Passed -- 3.6 3 78 22131 7
Test (3B): no agreement if too many followers disconnect ...
... Passed -- 3.8 5 172 40935 3
Test (3B): concurrent Start()s ...
... Passed -- 1.1 3 24 7379 6
Test (3B): rejoin of partitioned leader ...
... Passed -- 5.1 3 152 37021 4
Test (3B): leader backs up quickly over incorrect follower logs ...
... Passed -- 17.2 5 2080 1587388 102
Test (3B): RPC counts aren't too high ...
... Passed -- 2.2 3 60 20119 12
PASS
ok raft 35.557s

real 0m35.899s
user 0m2.556s
sys 0m1.458s
$
```

The "ok raft 35.557s" means that Go measured the time taken for the 3B tests to be 35.557 seconds of real (wall-clock) time. The "user 0m2.556s" means that the code consumed 2.556 seconds of CPU time, or time spent actually executing instructions (rather than waiting or sleeping). If your solution uses much more than a minute of real time for the 3B tests, or much more than 5 seconds of CPU time, you may run into trouble later on. Look for time spent sleeping or waiting for RPC timeouts, loops that run without sleeping or waiting for conditions or channel messages, or large numbers of RPCs sent.

## Files Agent Should Modify

The agent should implement the solution by modifying the following files:

- `src/raft/append_entries.go`
- `src/raft/election.go`
- `src/raft/install_snapshot.go`
- `src/raft/raft.go`
- `src/raft/util.go`

**Important**: Do not modify test files, configuration files, or other infrastructure files.
