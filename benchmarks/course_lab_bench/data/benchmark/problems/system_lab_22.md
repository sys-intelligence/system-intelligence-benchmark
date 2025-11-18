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
$ cd src/kvraft1
$ go test -v -run TestBasic4B
=== RUN   TestBasic4B
Test: one client (4B basic) (reliable network)...
    kvtest.go:62: Wrong error 
$
```

Now you will use the `rsm` package to replicate a key/value server. Each of the servers ("kvservers") will have an associated rsm/Raft peer. Clerks send `Put()` and `Get()` RPCs to the kvserver whose associated Raft is the leader. The kvserver code submits the Put/Get operation to `rsm`, which replicates it using Raft and invokes your server's `DoOp` at each peer, which should apply the operations to the peer's key/value database; the intent is for the servers to maintain identical replicas of the key/value database.

A `Clerk` sometimes doesn't know which kvserver is the Raft leader. If the `Clerk` sends an RPC to the wrong kvserver, or if it cannot reach the kvserver, the `Clerk` should re-try by sending to a different kvserver. If the key/value service commits the operation to its Raft log (and hence applies the operation to the key/value state machine), the leader reports the result to the `Clerk` by responding to its RPC. If the operation failed to commit (for example, if the leader was replaced), the server reports an error, and the `Clerk` retries with a different server.

Your kvservers should not directly communicate; they should only interact with each other through Raft.

Your first task is to implement a solution that works when there are no dropped messages, and no failed servers.

Feel free to copy your client code from Lab 2 (`kvsrv1/client.go`) into `kvraft1/client.go`. You will need to add logic for deciding which kvserver to send each RPC to.

You'll also need to implement `Put()` and `Get()` RPC handlers in `server.go`. These handlers should submit the request to Raft using `rsm.Submit()`. As the `rsm` package reads commands from `applyCh`, it should invoke the `DoOp` method, which you will have to implement in `server.go`.

You have completed this task when you **reliably** pass the first test in the test suite, with `go test -v -run TestBasic4B`.

- A kvserver should not complete a `Get()` RPC if it is not part of a majority (so that it does not serve stale data). A simple solution is to enter every `Get()` (as well as each `Put()`) in the Raft log using `Submit()`. You don't have to implement the optimization for read-only operations that is described in Section 8.
- It's best to add locking from the start because the need to avoid deadlocks sometimes affects overall code design. Check that your code is race-free using `go test -race`.

Now you should modify your solution to continue in the face of network and server failures. One problem you'll face is that a `Clerk` may have to send an RPC multiple times until it finds a kvserver that replies positively. If a leader fails just after committing an entry to the Raft log, the `Clerk` may not receive a reply, and thus may re-send the request to another leader. Each call to `Clerk.Put()` should result in just a single execution for a particular version number.

Add code to handle failures. Your `Clerk` can use a similar retry plan as in lab 2, including returning `ErrMaybe` if a response to a retried `Put` RPC is lost. You are done when your code reliably passes all the 4B tests, with `go test -v -run 4B`.

- Recall that the rsm leader may lose its leadership and return `rpc.ErrWrongLeader` from `Submit()`. In this case you should arrange for the Clerk to re-send the request to other servers until it finds the new leader.
- You will probably have to modify your Clerk to remember which server turned out to be the leader for the last RPC, and send the next RPC to that server first. This will avoid wasting time searching for the leader on every RPC, which may help you pass some of the tests quickly enough.

Your code should now pass the Lab 4B tests, like this:

```
$ cd kvraft1
$ go test -run 4B
Test: one client (4B basic) ...
  ... Passed --   3.2  5  1041  183
Test: one client (4B speed) ...
  ... Passed --  15.9  3  3169    0
Test: many clients (4B many clients) ...
  ... Passed --   3.9  5  3247  871
Test: unreliable net, many clients (4B unreliable net, many clients) ...
  ... Passed --   5.3  5  1035  167
Test: unreliable net, one client (4B progress in majority) ...
  ... Passed --   2.9  5   155    3
Test: no progress in minority (4B) ...
  ... Passed --   1.6  5   102    3
Test: completion after heal (4B) ...
  ... Passed --   1.3  5    67    4
Test: partitions, one client (4B partitions, one client) ...
  ... Passed --   6.2  5   958  155
Test: partitions, many clients (4B partitions, many clients (4B)) ...
  ... Passed --   6.8  5  3096  855
Test: restarts, one client (4B restarts, one client 4B ) ...
  ... Passed --   6.7  5   311   13
Test: restarts, many clients (4B restarts, many clients) ...
  ... Passed --   7.5  5  1223   95
Test: unreliable net, restarts, many clients (4B unreliable net, restarts, many clients ) ...
  ... Passed --   8.4  5   804   33
Test: restarts, partitions, many clients (4B restarts, partitions, many clients) ...
  ... Passed --  10.1  5  1308  105
Test: unreliable net, restarts, partitions, many clients (4B unreliable net, restarts, partitions, many clients) ...
  ... Passed --  11.9  5  1040   33
Test: unreliable net, restarts, partitions, random keys, many clients (4B unreliable net, restarts, partitions, random keys, many clients) ...
  ... Passed --  12.1  7  2801   93
PASS
ok      6.5840/kvraft1  103.797s
```

The numbers after each `Passed` are real time in seconds, number of peers, number of RPCs sent (including client RPCs), and number of key/value operations executed (`Clerk` Get/Put calls).
