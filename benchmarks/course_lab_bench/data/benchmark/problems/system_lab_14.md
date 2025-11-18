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

In many distributed applications, clients running on different machines use a key/value server to coordinate their activities. For example, ZooKeeper and Etcd allow clients to coordinate using a distributed lock, in analogy with how threads in a Go program can coordinate with locks (i.e., `sync.Mutex`). Zookeeper and Etcd implement such a lock with conditional put.

In this exercise your task is to implement a lock layered on client `Clerk.Put` and `Clerk.Get` calls. The lock supports two methods: `Acquire` and `Release`. The lock's specification is that only one client can successfully acquire the lock at a time; other clients must wait until the first client has released the lock using `Release`.

We supply you with skeleton code and tests in `src/kvsrv1/lock/`. You will need to modify `src/kvsrv1/lock/lock.go`. Your `Acquire` and `Release` code can talk to your key/value server by calling `lk.ck.Put()` and `lk.ck.Get()`.

If a client crashes while holding a lock, the lock will never be released. In a design more sophisticated than this lab, the client would attach a [lease](<https://en.wikipedia.org/wiki/Lease_(computer_science)#:~:text=Leases> are commonly used in,to rely on the resource.) to a lock. When the lease expires, the lock server would release the lock on behalf of the client. In this lab clients don't crash and you can ignore this problem.

Implement `Acquire` and `Release`. You have completed this exercise when your code passes the Reliable tests in the test suite in the lock sub-directory:

```
$ cd lock
$ go test -v -run Reliable
=== RUN   TestOneClientReliable
Test: 1 lock clients (reliable network)...
  ... Passed --   2.0  1   974    0
--- PASS: TestOneClientReliable (2.01s)
=== RUN   TestManyClientsReliable
Test: 10 lock clients (reliable network)...
  ... Passed --   2.1  1 83194    0
--- PASS: TestManyClientsReliable (2.11s)
PASS
ok   6.5840/kvsrv1/lock 4.120s
```

If you haven't implemented the lock yet, the first test will succeed.

This exercise requires little code but will require a bit more independent thought than the previous exercise.

- You will need a unique identifier for each lock client; call `kvtest.RandValue(8)` to generate a random string.
- The lock service should use a specific key to store the "lock state" (you would have to decide precisely what the lock state is). The key to be used is passed through the parameter `l` of `MakeLock` in `src/kvsrv1/lock/lock.go`.
