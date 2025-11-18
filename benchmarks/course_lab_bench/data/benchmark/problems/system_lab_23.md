# Problem Context

## Introduction

In this lab you will build a fault-tolerant key/value storage service using your Raft library from [Lab 3](http://nil.csail.mit.edu/6.5840/2025/labs/lab-raft1.html). To clients, the service looks similar to the server of [Lab 2](http://nil.csail.mit.edu/6.5840/2025/labs/lab-kvsrv1.html). However, instead of a single server, the service consists of a set of servers that use Raft to help them maintain identical databases. Your key/value service should continue to process client requests as long as a majority of the servers are alive and can communicate, in spite of other failures or network partitions. After Lab 4, you will have implemented all parts (Clerk, Service, and Raft) shown in the [diagram of Raft interactions](http://nil.csail.mit.edu/6.5840/2025/figs/kvraft.pdf).

Clients will interact with your key/value service through a Clerk, as in Lab 2. A Clerk implements the `Put` and `Get` methods with the same semantics as Lab 2: Puts are at-most-once and the Puts/Gets must form a linearizable history.

Providing linearizability is relatively easy for a single server. It is harder if the service is replicated, since all servers must choose the same execution order for concurrent requests, must avoid replying to clients using state that isn't up to date, and must recover their state after a failure in a way that preserves all acknowledged client updates.

This lab has three parts. In part A, you will implement a replicated-state machine package, `rsm`, using your raft implementation; `rsm` is agnostic of the requests that it replicates. In part B, you will implement a replicated key/value service using `rsm`, but without using snapshots. In part C, you will use your snapshot implementation from Lab 3D, which will allow Raft to discard old log entries. Please submit each part by the respective deadline.

You should review the [extended Raft paper](http://nil.csail.mit.edu/6.5840/2025/papers/raft-extended.pdf), in particular Section 7 (but not 8). For a wider perspective, have a look at Chubby, Paxos Made Live, Spanner, Zookeeper, Harp, Viewstamped Replication, and [Bolosky et al.](http://static.usenix.org/event/nsdi11/tech/full_papers/Bolosky.pdf) Start early.

## Getiting Started

We supply you with skeleton code and tests in `src/kvraft1`. The skeleton code uses the skeleton package `src/kvraft1/rsm` to replicate a server. A server must implement the `StateMachine` interface defined in `rsm` to replicate itself using `rsm`. Most of your work will be implementing `rsm` to provide server-agnostic replication. You will also need to modify `kvraft1/client.go` and `kvraft1/server.go` to implement the server-specific parts. This split allows you to re-use `rsm` in the next lab. You may be able to re-use some of your Lab 2 code (e.g., re-using the server code by copying or importing the `"src/kvsrv1"` package) but it is not a requirement.

To get up and running, execute the following commands. Don't forget the `git pull` to get the latest software.

```
$ cd ~/6.5840
$ git pull
..
```

## The Code

# Your Task

As things stand now, your key/value server doesn't call your Raft library's `Snapshot()` method, so a rebooting server has to replay the complete persisted Raft log in order to restore its state. Now you'll modify kvserver and `rsm` to cooperate with Raft to save log space and reduce restart time, using Raft's `Snapshot()` from Lab 3D.

The tester passes `maxraftstate` to your `StartKVServer()`, which passes it to `rsm`. `maxraftstate` indicates the maximum allowed size of your persistent Raft state in bytes (including the log, but not including snapshots). You should compare `maxraftstate` to `rf.PersistBytes()`. Whenever your `rsm` detects that the Raft state size is approaching this threshold, it should save a snapshot by calling Raft's `Snapshot`. `rsm` can create this snapshot by calling the `Snapshot` method of the `StateMachine` interface to obtain a snapshot of the kvserver. If `maxraftstate` is -1, you do not have to snapshot. The `maxraftstate` limit applies to the GOB-encoded bytes your Raft passes as the first argument to `persister.Save()`.

You can find the source for the `persister` object in `tester1/persister.go`.

Modify your rsm so that it detects when the persisted Raft state grows too large, and then hands a snapshot to Raft. When a `rsm` server restarts, it should read the snapshot with `persister.ReadSnapshot()` and, if the snapshot's length is greater than zero, pass the snapshot to the `StateMachine`'s `Restore()` method. You complete this task if you pass TestSnapshot4C in `rsm`.

```
$ cd kvraft1/rsm
$ go test -run TestSnapshot4C
=== RUN   TestSnapshot4C
  ... Passed --  9223372036.9  3   230    0
--- PASS: TestSnapshot4C (3.88s)
PASS
ok      6.5840/kvraft1/rsm      3.882s
```

- Think about when `rsm` should snapshot its state and what should be included in the snapshot beyond just the server state. Raft stores each snapshot in the persister object using `Save()`, along with corresponding Raft state. You can read the latest stored snapshot using `ReadSnapshot()`.
- Capitalize all fields of structures stored in the snapshot.

Implement the `kvraft1/server.go` `Snapshot()` and `Restore()` methods, which `rsm` calls. Modify `rsm` to handle applyCh messages that contain snapshots.

- You may have bugs in your Raft and rsm library that this task exposes. If you make changes to your Raft implementation make sure it continues to pass all of the Lab 3 tests.
- A reasonable amount of time to take for the Lab 4 tests is 400 seconds of real time and 700 seconds of CPU time.

Your code should pass the 4C tests (as in the example here) as well as the 4A+B tests (and your Raft must continue to pass the Lab 3 tests).

```
$ go test -run 4C
Test: snapshots, one client (4C SnapshotsRPC) ...
Test: InstallSnapshot RPC (4C) ...
  ... Passed --   4.5  3   241   64
Test: snapshots, one client (4C snapshot size is reasonable) ...
  ... Passed --  11.4  3  2526  800
Test: snapshots, one client (4C speed) ...
  ... Passed --  14.2  3  3149    0
Test: restarts, snapshots, one client (4C restarts, snapshots, one client) ...
  ... Passed --   6.8  5   305   13
Test: restarts, snapshots, many clients (4C restarts, snapshots, many clients ) ...
  ... Passed --   9.0  5  5583  795
Test: unreliable net, snapshots, many clients (4C unreliable net, snapshots, many clients) ...
  ... Passed --   4.7  5   977  155
Test: unreliable net, restarts, snapshots, many clients (4C unreliable net, restarts, snapshots, many clients) ...
  ... Passed --   8.6  5   847   33
Test: unreliable net, restarts, partitions, snapshots, many clients (4C unreliable net, restarts, partitions, snapshots, many clients) ...
  ... Passed --  11.5  5   841   33
Test: unreliable net, restarts, partitions, snapshots, random keys, many clients (4C unreliable net, restarts, partitions, snapshots, random keys, many clients) ...
  ... Passed --  12.8  7  2903   93
PASS
ok      6.5840/kvraft1  83.543s
```
