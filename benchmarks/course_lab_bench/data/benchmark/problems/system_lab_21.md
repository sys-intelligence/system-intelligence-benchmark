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

```
$ cd src/kvraft1/rsm
$ go test -v
=== RUN   TestBasic
Test RSM basic (reliable network)...
..
    config.go:147: one: took too long
```

In the common situation of a client/server service using Raft for replication, the service interacts with Raft in two ways: the service leader submits client operations by calling `raft.Start()`, and all service replicas receive committed operations via Raft's `applyCh`, which they execute. On the leader, these two activities interact. At any given time, some server goroutines are handling client requests, have called `raft.Start()`, and each is waiting for its operation to commit and to find out what the result of executing the operation is. And as committed operations appear on the `applyCh`, each needs to be executed by the service, and the results need to be handed to the goroutine that called `raft.Start()` so that it can return the result to the client.

The `rsm` package encapsulates the above interaction. It sits as a layer between the service (e.g. a key/value database) and Raft. In `rsm/rsm.go` you will need to implement a "reader" goroutine that reads the `applyCh`, and a `rsm.Submit()` function that calls `raft.Start()` for a client operation and then waits for the reader goroutine to hand it the result of executing that operation.

The service that is using `rsm` appears to the `rsm` reader goroutine as a `StateMachine` object providing a `DoOp()` method. The reader goroutine should hand each committed operation to `DoOp()`; `DoOp()`'s return value should be given to the corresponding `rsm.Submit()` call for it to return. `DoOp()`'s argument and return value have type `any`; the actual values should have the same types as the argument and return values that the service passes to `rsm.Submit()`, respectively.

The service should pass each client operation to `rsm.Submit()`. To help the reader goroutine match `applyCh` messages with waiting calls to `rsm.Submit()`, `Submit()` should wrap each client operation in an `Op` structure along with a unique identifier. `Submit()` should then wait until the operation has committed and been executed, and return the result of execution (the value returned by `DoOp()`). If `raft.Start()` indicates that the current peer is not the Raft leader, `Submit()` should return an `rpc.ErrWrongLeader` error. `Submit()` should detect and handle the situation in which leadership changed just after it called `raft.Start()`, causing the operation to be lost (never committed).

For Part A, the `rsm` tester acts as the service, submitting operations that it interprets as increments on a state consisting of a single integer. In Part B you'll use `rsm` as part of a key/value service that implements `StateMachine` (and `DoOp()`), and calls `rsm.Submit()`.

If all goes well, the sequence of events for a client request is:

- The client sends a request to the service leader.
- The service leader calls `rsm.Submit()` with the request.
- `rsm.Submit()` calls `raft.Start()` with the request, and then waits.
- Raft commits the request and sends it on all peers' `applyCh`s.
- The `rsm` reader goroutine on each peer reads the request from the `applyCh` and passes it to the service's `DoOp()`.
- On the leader, the `rsm` reader goroutine hands the `DoOp()` return value to the `Submit()` goroutine that originally submitted the request, and `Submit()` returns that value.

Your servers should not directly communicate; they should only interact with each other through Raft.

Implement `rsm.go`: the `Submit()` method and a reader goroutine. You have completed this task if you pass the `rsm` 4A tests:

```
  $ cd src/kvraft1/rsm
  $ go test -v -run 4A
=== RUN   TestBasic4A
Test RSM basic (reliable network)...
  ... Passed --   1.2  3    48    0
--- PASS: TestBasic4A (1.21s)
=== RUN   TestLeaderFailure4A
  ... Passed --  9223372036.9  3    31    0
--- PASS: TestLeaderFailure4A (1.50s)
PASS
ok      6.5840/kvraft1/rsm      2.887s
```

- You should not need to add any fields to the Raft `ApplyMsg`, or to Raft RPCs such as `AppendEntries`, but you are allowed to do so.
- Your solution needs to handle an `rsm` leader that has called `Start()` for a request submitted with `Submit()` but loses its leadership before the request is committed to the log. One way to do this is for the `rsm` to detect that it has lost leadership, by noticing that Raft's term has changed or a different request has appeared at the index returned by `Start()`, and return `rpc.ErrWrongLeader` from `Submit()`. If the ex-leader is partitioned by itself, it won't know about new leaders; but any client in the same partition won't be able to talk to a new leader either, so it's OK in this case for the server to wait indefinitely until the partition heals.
- The tester calls your Raft's `rf.Kill()` when it is shutting down a peer. Raft should close the `applyCh` so that your rsm learns about the shutdown, and can exit out of all loops.
