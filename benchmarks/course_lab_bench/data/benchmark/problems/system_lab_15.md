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

The main challenge in this exercise is that the network may re-order, delay, or discard RPC requests and/or replies. To recover from discarded requests/replies, the Clerk must keep re-trying each RPC until it receives a reply from the server.

If the network discards an RPC request message, then the client re-sending the request will solve the problem: the server will receive and execute just the re-sent request.

However, the network might instead discard an RPC reply message. The client does not know which message was discarded; the client only observes that it received no reply. If it was the reply that was discarded, and the client re-sends the RPC request, then the server will receive two copies of the request. That's OK for a `Get`, since `Get` doesn't modify the server state. It is safe to resend a `Put` RPC with the same version number, since the server executes `Put` conditionally on the version number; if the server received and executed a `Put` RPC, it will respond to a re-transmitted copy of that RPC with `rpc.ErrVersion` rather than executing the Put a second time.

A tricky case is if the server replies with an `rpc.ErrVersion` in a response to an RPC that the Clerk retried. In this case, the Clerk cannot know if the Clerk's `Put` was executed by the server or not: the first RPC might have been executed by the server but the network may have discarded the successful response from the server, so that the server sent `rpc.ErrVersion` only for the retransmitted RPC. Or, it might be that another Clerk updated the key before the Clerk's first RPC arrived at the server, so that the server executed neither of the Clerk's RPCs and replied `rpc.ErrVersion` to both. Therefore, if a Clerk receives `rpc.ErrVersion` for a retransmitted Put RPC, `Clerk.Put` must return `rpc.ErrMaybe` to the application instead of `rpc.ErrVersion` since the request may have been executed. It is then up to the application to handle this case. If the server responds to an initial (not retransmitted) Put RPC with `rpc.ErrVersion`, then the Clerk should return `rpc.ErrVersion` to the application, since the RPC was definitely not executed by the server.

It would be more convenient for application developers if `Put`'s were exactly-once (i.e., no `rpc.ErrMaybe` errors) but that is difficult to guarantee without maintaining state at the server for each Clerk. In the last exercise of this lab, you will implement a lock using your Clerk to explore how to program with at-most-once `Clerk.Put`.

Now you should modify your `kvsrv1/client.go` to continue in the face of dropped RPC requests and replies. A return value of `true` from the client's `ck.clnt.Call()` indicates that the client received an RPC reply from the server; a return value of `false` indicates that it did not receive a reply (more precisely, `Call()` waits for a reply message for a timeout interval, and returns false if no reply arrives within that time). Your `Clerk` should keep re-sending an RPC until it receives a reply. Keep in mind the discussion of `rpc.ErrMaybe` above. Your solution shouldn't require any changes to the server.

Add code to `Clerk` to retry if doesn't receive a reply. Your have completed this task if your code passes all tests in `kvsrv1/`, like this:

```
$ go test -v
=== RUN   TestReliablePut
One client and reliable Put (reliable network)...
  ... Passed --   0.0  1     5    0
--- PASS: TestReliablePut (0.00s)
=== RUN   TestPutConcurrentReliable
Test: many clients racing to put values to the same key (reliable network)...
info: linearizability check timed out, assuming history is ok
  ... Passed --   3.1  1 106647 106647
--- PASS: TestPutConcurrentReliable (3.09s)
=== RUN   TestMemPutManyClientsReliable
Test: memory use many put clients (reliable network)...
  ... Passed --   8.0  1 100000    0
--- PASS: TestMemPutManyClientsReliable (14.61s)
=== RUN   TestUnreliableNet
One client (unreliable network)...
  ... Passed --   7.6  1   251  208
--- PASS: TestUnreliableNet (7.60s)
PASS
ok   6.5840/kvsrv1 25.319s
```

- Before the client retries, it should wait a little bit; you can use go's `time` package and call `time.Sleep(100 * time.Millisecond)`
