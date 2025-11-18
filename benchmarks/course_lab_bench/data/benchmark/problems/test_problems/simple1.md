## Introduction

In this lab you will build a key/value server for a single machine that ensures that each operation is executed exactly once despite network failures and that the operations are linearizable. Later labs will replicate a server like this one to handle server crashes.

Clients can send three different RPCs to the key/value server: Put(key, value), Append(key, arg), and Get(key). The server maintains an in-memory map of key/value pairs. Keys and values are strings. Put(key, value) installs or replaces the value for a particular key in the map, Append(key, arg) appends arg to key's value and returns the old value, and Get(key) fetches the current value for the key. A Get for a non-existent key should return an empty string. An Append to a non-existent key should act as if the existing value were a zero-length string. Each client talks to the server through a Clerk with Put/Append/Get methods. A Clerk manages RPC interactions with the server.

Your server must arrange that application calls to Clerk Get/Put/Append methods be linearizable. If client requests aren't concurrent, each client Get/Put/Append call should observe the modifications to the state implied by the preceding sequence of calls. For concurrent calls, the return values and final state must be the same as if the operations had executed one at a time in some order. Calls are concurrent if they overlap in time: for example, if client X calls Clerk.Put(), and client Y calls Clerk.Append(), and then client X's call returns. A call must observe the effects of all calls that have completed before the call starts.

Linearizability is convenient for applications because it's the behavior you'd see from a single server that processes requests one at a time. For example, if one client gets a successful response from the server for an update request, subsequently launched reads from other clients are guaranteed to see the effects of that update. Providing linearizability is relatively easy for a single server.

## Getting Started

We supply you with skeleton code and tests in src/kvsrv. You will need to modify kvsrv/client.go, kvsrv/server.go, and kvsrv/common.go.

To get up and running, execute the following commands. Don't forget the git pull to get the latest software.

$ cd ~/6.5840
$ git pull
...
$ cd src/kvsrv
$ go test
...
$

## Task

Key/value server with no network failures (easy)

Run go test first (go test) to verify go environment is set up correctly.

Your first task is to implement a solution that works when there are no dropped messages.

You'll need to add RPC-sending code to the Clerk Put/Append/Get methods in client.go, and implement Put, Append() and Get() RPC handlers in server.go.

You have completed this task when you pass the first two tests in the test suite: "one client" and "many clients".

Check that your code is race-free using go test -race.

## Notes

if you encounter "build cache is required, but could not be located: GOCACHE is not defined and neither $XDG_CACHE_HOME nor $HOME are defined"
you can set `HOME` to `/tmp` and then try running the tests again.
If go is not sinatleld,  you can run the following command to install go:

```bash
apt-get update && apt-get install -y wget tar git build-essential && wget https://go.dev/dl/go1.22.3.linux-amd64.tar.gz && tar -C /usr/local -xzf go1.22.3.linux-amd64.tar.gz && rm go1.22.3.linux-amd64.tar.gz && apt-get clean && rm -rf /var/lib/apt/lists/* && export PATH="/usr/local/go/bin:${PATH}"
```

And run `go version` to check your go version
