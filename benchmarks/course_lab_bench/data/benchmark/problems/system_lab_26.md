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

In this part of the lab you will modify the controller to allow for concurrent controllers. When a controller crashes or is partitioned, the tester will start a new controller, which must finish any work that the old controller might have in progress (i.e., finishing moving shards like in Part B). This means that several controllers may run concurrently and send RPCs to the shardgrps and the `kvsrv` that stores configurations.

The main challenge is to ensure these controllers don't step on each other. In Part A you already fenced all the shardgrp RPCs with `Num` so that old RPCs are rejected. Even if several controllers pick up the work of an old controller concurrently, one of them succeeds and the others repeat all the RPCs, the shardgrps will ignore them.

Thus the challenging case left is to ensure that only one controller updates the next configuration to avoid that two controllers (e.g., a partitioned one and a new one) put different configurations in the next one. To stress this scenario, the tester runs several controllers concurrently and each one computes the next configuration by reading the current configuration and updating it for a shardgrp that left or joined, and then the tester invokes `ChangeConfigTo`; thus multiple controllers may invoke `ChangeConfigTo` with different configuration with the same `Num`. You can use the version number of a key and versioned `Put`s to ensure that only one controller updates the next configuration and that the other invocations return without doing anything.

Modify your controller so that only one controller can post a next configuration for a configuration `Num`. The tester will start many controllers but only one should start `ChangeConfigTo` for a new configuation. You have completed this task if you pass the concurrent tests of Part C:

```
$ cd ~/6.5840/src/shardkv1
$ go test -run TestConcurrentReliable5C
Test (5C): Concurrent ctrlers ... (reliable network)...
  ... Passed --  time  8.2s #peers 1 #RPCs  1753 #Ops  120
PASS
ok      6.5840/shardkv1 8.364s
$ go test -run TestAcquireLockConcurrentUnreliable5C
Test (5C): Concurrent ctrlers ... (unreliable network)...
  ... Passed --  time 23.8s #peers 1 #RPCs  1850 #Ops  120
PASS
ok      6.5840/shardkv1 24.008s
$
```

- See `concurCtrler` in `test.go` to see how the tester runs controllers concurrently.

In this exercise you will put recovery of an old controller together with a new controller: a new controller should perform recovery from Part B. If the old controller was partitioned during `ChangeConfigTo`, you will have to make sure that the old controller doesn't interfere with the new controller. If all the controller's updates are already properly fenced with `Num` checks from Part B, you don't have to write extra code. You have completed this task if you pass the `Partition` tests.

```
$ cd ~/6.5840/src/shardkv1
$ go test -run Partition
Test (5C): partition controller in join... (reliable network)...
  ... Passed --  time  7.8s #peers 1 #RPCs   876 #Ops  120
Test (5C): controllers with leased leadership ... (reliable network)...
  ... Passed --  time 36.8s #peers 1 #RPCs  3981 #Ops  360
Test (5C): controllers with leased leadership ... (unreliable network)...
  ... Passed --  time 52.4s #peers 1 #RPCs  2901 #Ops  240
Test (5C): controllers with leased leadership ... (reliable network)...
  ... Passed --  time 60.2s #peers 1 #RPCs 27415 #Ops 11182
Test (5C): controllers with leased leadership ... (unreliable network)...
  ... Passed --  time 60.5s #peers 1 #RPCs 11422 #Ops 2336
PASS
ok      6.5840/shardkv1 217.779s
$
```

You have completed implementing a highly-available sharded key/value service with many shard groups for scalability, reconfiguration to handle changes in load, and with a fault-tolerant controller; congrats!

Rerun all tests to check that your recent changes to the controller haven't broken earlier tests.

Gradescope will rerun the Lab 3A-D and Lab 4A-C tests on your submission, in addition to the 5C tests. Before submitting, double check that your solution works:

```
go test ./raft1
go test ./kvraft1
go test ./shardkv1
```
