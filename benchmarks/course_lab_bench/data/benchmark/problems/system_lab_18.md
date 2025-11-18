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

Implement the leader and follower code to append new log entries, so that the `go test -run 3B`tests pass.

- Run `git pull` to get the latest lab software.
- Raft log is 1-indexed, but we suggest that you view it as 0-indexed, and starting out with an entry (at index=0) that has term 0. That allows the very first AppendEntries RPC to contain 0 as PrevLogIndex, and be a valid index into the log.
- Your first goal should be to pass `TestBasicAgree3B()`. Start by implementing `Start()`, then write the code to send and receive new log entries via `AppendEntries` RPCs, following Figure 2. Send each newly committed entry on `applyCh` on each peer.
- You will need to implement the election restriction (section 5.4.1 in the paper).
- Your code may have loops that repeatedly check for certain events. Don't have these loops execute continuously without pausing, since that will slow your implementation enough that it fails tests. Use Go's [condition variables](https://golang.org/pkg/sync/#Cond), or insert a `time.Sleep(10 * time.Millisecond)` in each loop iteration.
- Do yourself a favor for future labs and write (or re-write) code that's clean and clear. For ideas, re-visit our the [Guidance page](http://nil.csail.mit.edu/6.5840/2025/labs/guidance.html) with tips on how to develop and debug your code.
- If you fail a test, look at `raft_test.go` and trace the test code from there to understand what's being tested.

The tests for upcoming labs may fail your code if it runs too slowly. You can check how much real time and CPU time your solution uses with the time command. Here's typical output:

```
$ time go test -run 3B
Test (3B): basic agreement (reliable network)...
  ... Passed --   1.3  3    18    0
Test (3B): RPC byte count (reliable network)...
  ... Passed --   2.8  3    56    0
Test (3B): test progressive failure of followers (reliable network)...
  ... Passed --   5.3  3   188    0
Test (3B): test failure of leaders (reliable network)...
  ... Passed --   6.4  3   378    0
Test (3B): agreement after follower reconnects (reliable network)...
  ... Passed --   5.9  3   176    0
Test (3B): no agreement if too many followers disconnect (reliable network)...
  ... Passed --   4.3  5   288    0
Test (3B): concurrent Start()s (reliable network)...
  ... Passed --   1.5  3    32    0
Test (3B): rejoin of partitioned leader (reliable network)...
  ... Passed --   5.3  3   216    0
Test (3B): leader backs up quickly over incorrect follower logs (reliable network)...
  ... Passed --  12.1  5  1528    0
Test (3B): RPC counts aren't too high (reliable network)...
  ... Passed --   3.1  3   106    0
PASS
ok      6.5840/raft1    48.353s
go test -run 3B  1.37s user 0.74s system 4% cpu 48.865 total
$
```

The "ok 6.5840/raft 35.557s" means that Go measured the time taken for the 3B tests to be 35.557 seconds of real (wall-clock) time. The "user 0m2.556s" means that the code consumed 2.556 seconds of CPU time, or time spent actually executing instructions (rather than waiting or sleeping). If your solution uses much more than a minute of real time for the 3B tests, or much more than 5 seconds of CPU time, you may run into trouble later on. Look for time spent sleeping or waiting for RPC timeouts, loops that run without sleeping or waiting for conditions or channel messages, or large numbers of RPCs sent.
