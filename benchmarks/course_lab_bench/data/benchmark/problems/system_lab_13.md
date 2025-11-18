# Problem Context

## Introduction

In this lab you will build a key/value server for a single machine that ensures that each Put operation is executed *at-most-once* despite network failures and that the operations are *linearizable*. You will use this KV server to implement a lock. Later labs will replicate a server like this one to handle server crashes.

### KV server

Each client interacts with the key/value server using a *Clerk*, which sends RPCs to the server. Clients can send two different RPCs to the server: `Put(key, value, version)` and `Get(key)`. The server maintains an in-memory map that records for each key a (value, version) tuple. Keys and values are strings. The version number records the number of times the key has been written. `Put(key, value, version)` installs or replaces the value for a particular key in the map *only if* the `Put`'s version number matches the server's version number for the key. If the version numbers match, the server also increments the version number of the key. If the version numbers don't match, the server should return `rpc.ErrVersion`. A client can create a new key by invoking `Put` with version number 0 (and the resulting version stored by the server will be 1). If the version number of the `Put` is larger than 0 and the key doesn't exist, the server should return `rpc.ErrNoKey`.

`Get(key)` fetches the current value for the key and its associated version. If the key doesn't exist at the server, the server should return `rpc.ErrNoKey`.

Maintaining a version number for each key will be useful for implementing locks using `Put` and ensuring at-most-once semantics for `Put`'s when the network is unreliable and the client retransmits.

When you've finished this lab and passed all the tests, you'll have a *linearizable* key/value service from the point of view of clients calling `Clerk.Get` and `Clerk.Put`. That is, if client operations aren't concurrent, each client `Clerk.Get` and `Clerk.Put` will observe the modifications to the state implied by the preceding sequence of operations. For concurrent operations, the return values and final state will be the same as if the operations had executed one at a time in some order. Operations are concurrent if they overlap in time: for example, if client X calls `Clerk.Put()`, and client Y calls `Clerk.Put()`, and then client X's call returns. An operation must observe the effects of all operations that have completed before the operation starts. See the FAQ on [linearizability](http://nil.csail.mit.edu/6.5840/2025/papers/linearizability-faq.txt) for more background.

Linearizability is convenient for applications because it's the behavior you'd see from a single server that processes requests one at a time. For example, if one client gets a successful response from the server for an update request, subsequently launched reads from other clients are guaranteed to see the effects of that update. Providing linearizability is relatively easy for a single server.

## Getiting Started

We supply you with skeleton code and tests in `src/kvsrv1`. `kvsrv1/client.go` implements a Clerk that clients use to manage RPC interactions with the server; the Clerk provides `Put` and `Get` methods. `kvsrv1/server.go` contains the server code, including the `Put` and `Get` handlers that implement the server side of RPC requests. You will need to modify `client.go` and `server.go`. The RPC requests, replies, and error values are defined in the `kvsrv1/rpc` package in the file `kvsrv1/rpc/rpc.go`, which you should look at, though you don't have to modify `rpc.go`.

To get up and running, execute the following commands. Don't forget the `git pull` to get the latest software.

```
$ cd ~/6.5840
$ git pull
...
$ cd src/kvsrv1
$ go test -v
=== RUN   TestReliablePut
One client and reliable Put (reliable network)...
    kvsrv_test.go:25: Put err ErrNoKey
...
$
```

## The Code

# Your Task

Your first task is to implement a solution that works when there are no dropped messages. You'll need to add RPC-sending code to the Clerk Put/Get methods in `client.go`, and implement `Put` and `Get` RPC handlers in `server.go`.

You have completed this task when you pass the Reliable tests in the test suite:

```
$ go test -v -run Reliable
=== RUN   TestReliablePut
One client and reliable Put (reliable network)...
  ... Passed --   0.0  1     5    0
--- PASS: TestReliablePut (0.00s)
=== RUN   TestPutConcurrentReliable
Test: many clients racing to put values to the same key (reliable network)...
info: linearizability check timed out, assuming history is ok
  ... Passed --   3.1  1 90171 90171
--- PASS: TestPutConcurrentReliable (3.07s)
=== RUN   TestMemPutManyClientsReliable
Test: memory use many put clients (reliable network)...
  ... Passed --   9.2  1 100000    0
--- PASS: TestMemPutManyClientsReliable (16.59s)
PASS
ok   6.5840/kvsrv1 19.681s
```

The numbers after each `Passed` are real time in seconds, the constant 1, the number of RPCs sent (including client RPCs), and the number of key/value operations executed (`Clerk` `Get` and `Put` calls).

- Check that your code is race-free using `go test -race`.
