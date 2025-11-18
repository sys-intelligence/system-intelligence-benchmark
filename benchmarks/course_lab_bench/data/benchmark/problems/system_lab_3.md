# Problem Context

## Introduction

In this lab you will build a key/value server for a single machine that ensures that each operation is executed exactly once despite network failures and that the operations are [linearizable](http://nil.csail.mit.edu/6.5840/2024/papers/linearizability-faq.txt). Later labs will replicate a server like this one to handle server crashes.

Clients can send three different RPCs to the key/value server: `Put(key, value)`, `Append(key, arg)`, and `Get(key)`. The server maintains an in-memory map of key/value pairs. Keys and values are strings. `Put(key, value)` installs or replaces the value for a particular key in the map, `Append(key, arg)` appends arg to key's value *and* returns the old value, and `Get(key)` fetches the current value for the key. A `Get` for a non-existent key should return an empty string. An `Append` to a non-existent key should act as if the existing value were a zero-length string. Each client talks to the server through a `Clerk` with Put/Append/Get methods. A `Clerk` manages RPC interactions with the server.

Your server must arrange that application calls to `Clerk` Get/Put/Append methods be linearizable. If client requests aren't concurrent, each client Get/Put/Append call should observe the modifications to the state implied by the preceding sequence of calls. For concurrent calls, the return values and final state must be the same as if the operations had executed one at a time in some order. Calls are concurrent if they overlap in time: for example, if client X calls `Clerk.Put()`, and client Y calls `Clerk.Append()`, and then client X's call returns. A call must observe the effects of all calls that have completed before the call starts.

Linearizability is convenient for applications because it's the behavior you'd see from a single server that processes requests one at a time. For example, if one client gets a successful response from the server for an update request, subsequently launched reads from other clients are guaranteed to see the effects of that update. Providing linearizability is relatively easy for a single server.

## Getiting Started

We supply you with skeleton code and tests in `src/kvsrv`. You will need to modify `kvsrv/client.go`, `kvsrv/server.go`, and `kvsrv/common.go`.

To get up and running, execute the following commands. Don't forget the `git pull` to get the latest software.

```
$ cd ~/6.5840
$ git pull
...
$ cd src/kvsrv
$ go test
...
$
```

## The Code

# Your Task

Now you should modify your solution to continue in the face of dropped messages (e.g., RPC requests and RPC replies). If a message was lost, then the client's `ck.server.Call()` will return `false` (more precisely, `Call()` waits for a reply message for a timeout interval, and returns false if no reply arrives within that time). One problem you'll face is that a `Clerk` may have to send an RPC multiple times until it succeeds. Each call to `Clerk.Put()` or `Clerk.Append()`, however, should result in just a *single* execution, so you will have to ensure that the re-send doesn't result in the server executing the request twice.

Add code to `Clerk` to retry if doesn't receive a reply, and to `server.go` to filter duplicates if the operation requires it. These notes include guidance on [duplicate detection](http://nil.csail.mit.edu/6.5840/2024/notes/l-raft-QA.txt).

- You will need to uniquely identify client operations to ensure that the key/value server executes each one just once.
- You will have to think carefully about what state the server must maintain for handling duplicate `Get()`, `Put()`, and `Append()` requests, if any at all.
- Your scheme for duplicate detection should free server memory quickly, for example by having each RPC imply that the client has seen the reply for its previous RPC. It's OK to assume that a client will make only one call into a Clerk at a time.

Your code should now pass all tests, like this:

```
$ go test
Test: one client ...
  ... Passed -- t  3.8 nrpc 31135 ops 31135
Test: many clients ...
  ... Passed -- t  4.7 nrpc 102853 ops 102853
Test: unreliable net, many clients ...
  ... Passed -- t  4.1 nrpc   580 ops  496
Test: concurrent append to same key, unreliable ...
  ... Passed -- t  0.6 nrpc    61 ops   52
Test: memory use get ...
  ... Passed -- t  0.4 nrpc     4 ops    0
Test: memory use put ...
  ... Passed -- t  0.2 nrpc     2 ops    0
Test: memory use append ...
  ... Passed -- t  0.4 nrpc     2 ops    0
Test: memory use many puts ...
  ... Passed -- t 11.5 nrpc 100000 ops    0
Test: memory use many gets ...
  ... Passed -- t 12.2 nrpc 100001 ops    0
PASS
ok      6.5840/kvsrv    39.000s
```

The numbers after each `Passed` are real time in seconds, number of RPCs sent (including client RPCs), and number of key/value operations executed (`Clerk` Get/Put/Append calls).
