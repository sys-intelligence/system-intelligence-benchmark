# Problem Context

## Introduction

You can either do a [final project](http://nil.csail.mit.edu/6.5840/2025/project.html) based on your own ideas, or this lab.

In this lab you'll build a key/value storage system that "shards," or partitions, the keys over a set of Raft-replicated key/value server groups (shardgrps). A shard is a subset of the key/value pairs; for example, all the keys starting with "a" might be one shard, all the keys starting with "b" another, etc. The reason for sharding is performance. Each shardgrp handles puts and gets for just a few of the shards, and the shardgrps operate in parallel; thus total system throughput (puts and gets per unit time) increases in proportion to the number of shardgrps.

![shardkv design](http://nil.csail.mit.edu/6.5840/2025/labs/shardkv.png)

The sharded key/value service has the components shown above. Shardgrps (shown with blue squares) store shards with keys: shardgrp 1 holds a shard storing key "a", and shardgrp 2 holds a shard storing key "b". Clients of the sharded key/value service interact with the service through a clerk (shown with a green circle), which implements `Get` and `Put` methods. To find the shardgrp for a key passed to `Put`/`Get`, the clerk gets the configuration from the kvsrv (shown with a black square), which you implemented in Lab 2. The configuration (not shown) describes the mapping from shards to shardgrps (e.g., shard 1 is served by shardgrp 3).

An administrator (i.e., the tester) uses another client, the controller (shown with a purple circle), to add/remove shardgrps from the cluster and update which shardgrp should serve a shard. The controller has one main method: `ChangeConfigTo`, which takes as argument a new configuration and changes the system from the current configuration to the new configuration; this involves moving shards to new shardgrps that are joining the system and moving shards away from shardgrps that are leaving the system. To do so the controller 1) makes RPCs (`FreezeShard`, `InstallShard`, and `DeleteShard`) to shardgrps, and 2) updates the configuration stored in kvsrv.

The reason for the controller is that a sharded storage system must be able to shift shards among shardgrps. One reason is that some shardgrps may become more loaded than others, so that shards need to be moved to balance the load. Another reason is that shardgrps may join and leave the system: new shardgrps may be added to increase capacity, or existing shardgrps may be taken offline for repair or retirement.

The main challenges in this lab will be ensuring linearizability of `Get`/`Put` operations while handling 1) changes in the assignment of shards to shardgrps, and 2) recovering from a controller that fails or is partitioned during `ChangeConfigTo`.

1. `ChangeConfigTo` moves shards from one shardgrp to another. A risk is that some clients might use the old shardgrp while other clients use the new shardgrp, which could break linearizability. You will need to ensure that at most one shardgrp is serving requests for each shard at any one time.
2. If `ChangeConfigTo` fails while reconfiguring, some shards may be inaccessible if they have started but not completed moving from one shardgrp to another. To make forward progress, the tester starts a new controller, and your job is to ensure that the new one completes the reconfiguration that the previous controller started.

This lab uses "configuration" to refer to the assignment of shards to shardgrps. This is not the same as Raft cluster membership changes. You don't have to implement Raft cluster membership changes.

A shardgrp server is a member of only a single shardgrp. The set of servers in a given shardgrp will never change.

Only RPC may be used for interaction among clients and servers. For example, different instances of your server are not allowed to share Go variables or files.

In Part A, you will implement a working `shardctrler`, which will store and retrieve configurations in a `kvsrv`. You will also implement the `shardgrp`, replicated with your Raft `rsm` package, and a corresponding `shardgrp` clerk. The `shardctrler` talks to the `shardgrp` clerks to move shards between different groups.

In Part B, you will modify your `shardctrler` to handle failures and partitions during config changes. In Part C, you will extend your `shardctrler` to allow for concurrent controllers without interfering with each other. Finally, in Part D, you will have the opportunity to extend your solution in any way you like.

This lab's sharded key/value service follows the same general design as Flat Datacenter Storage, BigTable, Spanner, FAWN, Apache HBase, Rosebud, Spinnaker, and many others. These systems differ in many details from this lab, though, and are also typically more sophisticated and capable. For example, the lab doesn't evolve the sets of peers in each Raft group; its data and query models are simple; and so on.

Lab 5 will use your `kvsrv` from Lab 2, and your `rsm` and `Raft` from Lab 4. Your Lab 5 and Lab 4 must use the same `rsm` and `Raft` implementations.

You may use late hours for Part A, but you may not use late hours for Parts B-D.

## Getiting Started

Do a `git pull` to get the latest lab software.

We supply you with tests and skeleton code in `src/shardkv1`:

- `client.go` for the shardkv clerk
- `shardcfg` package for computing shard configurations
- `shardgrp` package: for the shardgrp clerk and server.
- `shardctrler` package, which contains `shardctrler.go` with methods for the controller to change a configuration (`ChangeConfigTo`) and to get a configuration (`Query`)

To get up and running, execute the following commands:

```
$ cd ~/6.5840
$ git pull
...
$ cd src/shardkv1
$ go test -v
=== RUN  TestInitQuery5A
Test (5A): Init and Query ... (reliable network)...
    shardkv_test.go:46: Static wrong null 0
...
```

## The Code

# Your Task

Your first job is to implement shardgrps and the `InitConfig`, `Query`, and `ChangeConfigTo` methods when there are no failures. We have given you the code for describing a configuration, in `shardkv1/shardcfg`. Each `shardcfg.ShardConfig` has a unique identifying number, a mapping from shard number to group number, and a mapping from group number to the list of servers replicating that group. There will usually be more shards than groups (so that each group serves more than one shard), in order that load can be shifted at a fairly fine granularity.

Implement these two methods in `shardctrler/shardctrler.go`:

- The `InitConfig` method receives the first configuration, passed to it by the tester as a `shardcfg.ShardConfig`. `InitConfig` should store the configuration in an instance of Lab 2's `kvsrv`.
- The `Query` method returns the current configuration; it should read the configuration from `kvsrv`, previously stored there by `InitConfig`.

Implement `InitConfig` and `Query`, and store the configuration in `kvsrv`. You're done when your code passes the first test. Note this task doesn't require any shardgrps.

```
$ cd ~/6.5840/src/shardkv1
$ go test -run TestInitQuery5A                   
Test (5A): Init and Query ... (reliable network)...
  ... Passed --  time  0.0s #peers 1 #RPCs     3 #Ops    0
PASS
ok      6.5840/shardkv1 0.197s
$
```

- Implement `InitConfig` and `Query` by storing and reading the initial configuration from `kvsrv`: use the `Get`/`Put` methods of `ShardCtrler.IKVClerk` to talk to `kvsrv`, use the `String` method of `ShardConfig` to turn a `ShardConfig` into a string that you can pass to `Put`, and use the `shardcfg.FromString()` function to turn a string into a `ShardConfig`.

Implement an initial version of `shardgrp` in `shardkv1/shardgrp/server.go` and a corresponding clerk in `shardkv1/shardgrp/client.go` by copying code from your Lab 4 `kvraft` solution.

Implement a clerk in `shardkv1/client.go` that uses the `Query` method to find the shardgrp for a key, and then talks to that shardgrp. You're done when your code passes the `Static` test.

```
$ cd ~/6.5840/src/shardkv1
$ go test -run Static
Test (5A): one shard group ... (reliable network)...
  ... Passed --  time  5.4s #peers 1 #RPCs   793 #Ops  180
PASS
ok      6.5840/shardkv1 5.632s
$
```

- Copy code from your `kvraft` client.go and server.go for `Put` and `Get`, and any other code you need from `kvraft`.
- The code in `shardkv1/client.go` provides the `Put`/`Get` clerk for the overall system: it finds out which shardgrp holds the desired key's shard by invoking the `Query` method, and then talks to the shardgrp that holds that shard.
- Implement `shardkv1/client.go`, including its `Put`/`Get` methods. Use `shardcfg.Key2Shard()` to find the shard number for a key. The tester passes a `ShardCtrler` object to `MakeClerk` in `shardkv1/client.go`. Retrieve the current configuration using the `Query` method.
- To put/get a key from a shardgrp, the shardkv clerk should create a shardgrp clerk for the shardgrp by calling `shardgrp.MakeClerk`, passing in the servers found in the configuration and the shardkv clerk's `ck.clnt`. Use the `GidServers()` method from `ShardConfig` to get the group for a shard.
- `shardkv1/client.go`'s Put must return `ErrMaybe` when the reply was maybe lost, but this Put invokes `shardgrp`'s Put to talk a particular shardgrp. The inner Put can signal this with an error.
- Upon creation, the first shardgrp (`shardcfg.Gid1`) should initialize itself to own all shards.

Now you should support movement of shards among groups by implementing the `ChangeConfigTo` method, which changes from an old configuration to a new configuration. The new configuration may include new shardgrps that are not present in the old configuration, and may exclude shardgrps that were present in the old configuration. The controller should move shards (the key/value data) so that the set of shards stored by each shardgrp matches the new configuration.

The approach we suggest for moving a shard is for `ChangeConfigTo` to first "freeze" the shard at the source shardgrp, causing that shardgrp to reject `Put`'s for keys in the moving shard. Then, copy (install) the shard to the destination shardgrp; then delete the frozen shard. Finally, post a new configuration so that clients can find the moved shard. A nice property of this approach is that it avoids any direct interactions among the shardgrps. It also supports serving shards that are not affected by an ongoing configuration change.

To be able to order changes to the configuration, each configuration has a unique number `Num` (see `shardcfg/shardcfg.go`). The tester in Part A invokes `ChangeConfigTo` sequentially, and the configuration passed to `ChangeConfigTo` will have a `Num` one larger than the previous one; thus, a configuration with a higher `Num` is newer than one with a lower `Num`.

The network may delay RPCs, and RPCs may arrive out of order at the shardgrps. To reject old `FreezeShard`, `InstallShard`, and `DeleteShard` RPCs, they should include `Num` (see `shardgrp/shardrpc/shardrpc.go`), and shardgrps must remember the largest `Num` they have seen for each shard.

Implement `ChangeConfigTo` (in `shardctrler/shardctrler.go`) and extend `shardgrp` to support freeze, install, and delete. `ChangeConfigTo` should always succeed in Part A because the tester doesn't induce failures in this part. You will need to implement `FreezeShard`, `InstallShard`, and `DeleteShard` in `shardgrp/client.go` and `shardgrp/server.go` using the RPCs in the `shardgrp/shardrpc` package, and reject old RPCs based on `Num`. You will also need modify the shardkv clerk in `shardkv1/client.go` to handle `ErrWrongGroup`, which a shardgrp should return if it isn't responsible for the shard.

You have completed this task when you pass the `JoinBasic` and `DeleteBasic` tests. These tests focus on adding shardgrps; you don't have to worry about shardgrps leaving just yet.

- A shardgrp should respond with an `ErrWrongGroup` error to a client `Put`/`Get` with a key that the shardgrp isn't responsible for (i.e., for a key whose shard is not assigned to the shardgrp). You will have to modify `shardkv1/client.go` to reread the configuration and retry the `Put`/`Get`.
- Note that you will have to run `FreezeShard`, `InstallShard`, and `DeleteShard` through your `rsm` package, just like `Put` and `Get`.
- You can send an entire map as your state in an RPC request or reply, which may help keep the code for shard transfer simple.
- If one of your RPC handlers includes in its reply a map (e.g. a key/value map) that's part of your server's state, you may get bugs due to races. The RPC system has to read the map in order to send it to the caller, but it isn't holding a lock that covers the map. Your server, however, may proceed to modify the same map while the RPC system is reading it. The solution is for the RPC handler to include a copy of the map in the reply.

Extend `ChangeConfigTo` to handle shard groups that leave; i.e., shardgrps that are present in the current configuration but not in the new one. Your solution should pass `TestJoinLeaveBasic5A` now. (You may have handled this scenario already in the previous task, but the previous tests didn't test for shardgrps leaving.)

Make your solution pass all Part A tests, which check that your sharded key/value service supports many groups joining and leaving, shardgrps restarting from snapshots, processing `Get`s while some shards are offline or involved in a configuration change, and linearizability when many clients interact with the service while the tester concurrently invokes the controller's `ChangeConfigTo` to rebalance shards.

```
$ cd ~/6.5840/src/shardkv1
$ go test -run 5A
Test (5A): Init and Query ... (reliable network)...
  ... Passed --  time  0.0s #peers 1 #RPCs     3 #Ops    0
Test (5A): one shard group ... (reliable network)...
  ... Passed --  time  5.1s #peers 1 #RPCs   792 #Ops  180
Test (5A): a group joins... (reliable network)...
  ... Passed --  time 12.9s #peers 1 #RPCs  6300 #Ops  180
Test (5A): delete ... (reliable network)...
  ... Passed --  time  8.4s #peers 1 #RPCs  1533 #Ops  360
Test (5A): basic groups join/leave ... (reliable network)...
  ... Passed --  time 13.7s #peers 1 #RPCs  5676 #Ops  240
Test (5A): many groups join/leave ... (reliable network)...
  ... Passed --  time 22.1s #peers 1 #RPCs  3529 #Ops  180
Test (5A): many groups join/leave ... (unreliable network)...
  ... Passed --  time 54.8s #peers 1 #RPCs  5055 #Ops  180
Test (5A): shutdown ... (reliable network)...
  ... Passed --  time 11.7s #peers 1 #RPCs  2807 #Ops  180
Test (5A): progress ... (reliable network)...
  ... Passed --  time  8.8s #peers 1 #RPCs   974 #Ops   82
Test (5A): progress ... (reliable network)...
  ... Passed --  time 13.9s #peers 1 #RPCs  2443 #Ops  390
Test (5A): one concurrent clerk reliable... (reliable network)...
  ... Passed --  time 20.0s #peers 1 #RPCs  5326 #Ops 1248
Test (5A): many concurrent clerks reliable... (reliable network)...
  ... Passed --  time 20.4s #peers 1 #RPCs 21688 #Ops 10500
Test (5A): one concurrent clerk unreliable ... (unreliable network)...
  ... Passed --  time 25.8s #peers 1 #RPCs  2654 #Ops  176
Test (5A): many concurrent clerks unreliable... (unreliable network)...
  ... Passed --  time 25.3s #peers 1 #RPCs  7553 #Ops 1896
PASS
ok      6.5840/shardkv1 243.115s
$
```

Your solution must continue serving shards that are not affected by an ongoing configuration change.
