# Problem Context

## Introduction

In this lab you will build a fault-tolerant key/value storage service using your Raft library from [Lab 3](http://nil.csail.mit.edu/6.5840/2024/labs/lab-raft.html). Your key/value service will be a replicated state machine, consisting of several key/value servers that each maintain a database of key/value pairs, as in [Lab 2](http://nil.csail.mit.edu/6.5840/2024/labs/lab-raft.html), but additionally use Raft for replication. Your key/value service should continue to process client requests as long as a majority of the servers are alive and can communicate, in spite of other failures or network partitions. After Lab 4, you will have implemented all parts (Clerk, Service, and Raft) shown in the [diagram of Raft interactions](http://nil.csail.mit.edu/6.5840/2024/notes/raft_diagram.pdf).

Clients will interact with your key/value service in much the same way as Lab 2. In particular, clients can send three different RPCs to the key/value service:

- `Put(key, value)`: replaces the value for a particular key in the database
- `Append(key, arg)`: appends arg to key's value (treating the existing value as an empty string if the key is non-existent)
- `Get(key)`: fetches the current value of the key (returning the empty string for non-existent keys)

Keys and values are strings. Note that unlike in Lab 2, neither `Put` nor `Append` should return a value to the client. Each client talks to the service through a `Clerk` with Put/Append/Get methods. The `Clerk` manages RPC interactions with the servers.

Your service must arrange that application calls to `Clerk` Get/Put/Append methods be linearizable. If called one at a time, the Get/Put/Append methods should act as if the system had only one copy of its state, and each call should observe the modifications to the state implied by the preceding sequence of calls. For concurrent calls, the return values and final state must be the same as if the operations had executed one at a time in some order. Calls are concurrent if they overlap in time: for example, if client X calls `Clerk.Put()`, and client Y calls `Clerk.Append()`, and then client X's call returns. A call must observe the effects of all calls that have completed before the call starts.

Providing linearizability is relatively easy for a single server. It is harder if the service is replicated, since all servers must choose the same execution order for concurrent requests, must avoid replying to clients using state that isn't up to date, and must recover their state after a failure in a way that preserves all acknowledged client updates.

This lab has two parts. In part A, you will implement a replicated key/value service using your Raft implementation, but without using snapshots. In part B, you will use your snapshot implementation from Lab 3D, which will allow Raft to discard old log entries. Please submit each part by the respective deadline.

You should review the [extended Raft paper](http://nil.csail.mit.edu/6.5840/2024/papers/raft-extended.pdf), in particular Sections 7 and 8. For a wider perspective, have a look at Chubby, Paxos Made Live, Spanner, Zookeeper, Harp, Viewstamped Replication, and [Bolosky et al.](http://static.usenix.org/event/nsdi11/tech/full_papers/Bolosky.pdf)

Start early.

## Getiting Started

We supply you with skeleton code and tests in `src/kvraft`. You will need to modify `kvraft/client.go`, `kvraft/server.go`, and perhaps `kvraft/common.go`.

To get up and running, execute the following commands. Don't forget the `git pull` to get the latest software.

```
$ cd ~/6.5840
$ git pull
...
$ cd src/kvraft
$ go test
...
$
```

## The Code

# Your Task

As things stand now, your key/value server doesn't call your Raft library's `Snapshot()` method, so a rebooting server has to replay the complete persisted Raft log in order to restore its state. Now you'll modify kvserver to cooperate with Raft to save log space, and reduce restart time, using Raft's `Snapshot()` from Lab 3D.

The tester passes `maxraftstate` to your `StartKVServer()`. `maxraftstate` indicates the maximum allowed size of your persistent Raft state in bytes (including the log, but not including snapshots). You should compare `maxraftstate` to `persister.RaftStateSize()`. Whenever your key/value server detects that the Raft state size is approaching this threshold, it should save a snapshot by calling Raft's `Snapshot`. If `maxraftstate` is -1, you do not have to snapshot. `maxraftstate` applies to the GOB-encoded bytes your Raft passes as the first argument to to `persister.Save()`.

Modify your kvserver so that it detects when the persisted Raft state grows too large, and then hands a snapshot to Raft. When a kvserver server restarts, it should read the snapshot from `persister` and restore its state from the snapshot.

- Think about when a kvserver should snapshot its state and what should be included in the snapshot. Raft stores each snapshot in the persister object using `Save()`, along with corresponding Raft state. You can read the latest stored snapshot using `ReadSnapshot()`.
- Your kvserver must be able to detect duplicated operations in the log across checkpoints, so any state you are using to detect them must be included in the snapshots.
- Capitalize all fields of structures stored in the snapshot.
- You may have bugs in your Raft library that this lab exposes. If you make changes to your Raft implementation make sure it continues to pass all of the Lab 3 tests.
- A reasonable amount of time to take for the Lab 4 tests is 400 seconds of real time and 700 seconds of CPU time. Further, `go test -run TestSnapshotSize` should take less than 20 seconds of real time.

Your code should pass the 4B tests (as in the example here) as well as the 4A tests (and your Raft must continue to pass the Lab 3 tests).

```
$ go test -run 4B
Test: InstallSnapshot RPC (4B) ...
  ... Passed --   4.0  3   289   63
Test: snapshot size is reasonable (4B) ...
  ... Passed --   2.6  3  2418  800
Test: ops complete fast enough (4B) ...
  ... Passed --   3.2  3  3025    0
Test: restarts, snapshots, one client (4B) ...
  ... Passed --  21.9  5 29266 5820
Test: restarts, snapshots, many clients (4B) ...
  ... Passed --  21.5  5 33115 6420
Test: unreliable net, snapshots, many clients (4B) ...
  ... Passed --  17.4  5  3233  482
Test: unreliable net, restarts, snapshots, many clients (4B) ...
  ... Passed --  22.7  5  3337  471
Test: unreliable net, restarts, partitions, snapshots, many clients (4B) ...
  ... Passed --  30.4  5  2725  274
Test: unreliable net, restarts, partitions, snapshots, random keys, many clients (4B) ...
  ... Passed --  37.7  7  8378  681
PASS
ok   6.5840/kvraft 161.538s
```
