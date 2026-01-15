# Sharded Key/Value Service

### Introduction

In this lab you'll build a key/value storage system that "shards," or partitions, the keys over a set of replica groups. A shard is a subset of the key/value pairs; for example, all the keys starting with "a" might be one shard, all the keys starting with "b" another, etc. The reason for sharding is performance. Each replica group handles puts and gets for just a few of the shards, and the groups operate in parallel; thus total system throughput (puts and gets per unit time) increases in proportion to the number of groups.

Your sharded key/value store will have two main components. First, a set of replica groups. Each replica group is responsible for a subset of the shards, using Raft replication. The second component is the "shard controller". The shard controller decides which replica group should serve each shard; this information is called the configuration. The configuration changes over time. Clients consult the shard controller in order to find the replica group for a key, and replica groups consult the controller in order to find out what shards to serve. There is a single shard controller for the whole system, implemented as a fault-tolerant service using Raft.

A sharded storage system must be able to shift shards among replica groups. One reason is that some groups may become more loaded than others, so that shards need to be moved to balance the load. Another reason is that replica groups may join and leave the system: new replica groups may be added to increase capacity, or existing replica groups may be taken offline for repair or retirement.

The main challenge in this lab will be handling reconfiguration -- changes in the assignment of shards to groups. Within a single replica group, all group members must agree on when a reconfiguration occurs relative to client Put/Append/Get requests. For example, a Put may arrive at about the same time as a reconfiguration that causes the replica group to stop being responsible for the shard holding the Put's key. All replicas in the group must agree on whether the Put occurred before or after the reconfiguration. If before, the Put should take effect and the new owner of the shard will see its effect; if after, the Put won't take effect and client must re-try at the new owner. The recommended approach is to have each replica group use Raft to log not just the sequence of Puts, Appends, and Gets but also the sequence of reconfigurations. You will need to ensure that at most one replica group is serving requests for each shard at any one time.

Reconfiguration also requires interaction among the replica groups. For example, in configuration 10 group G1 may be responsible for shard S1. In configuration 11, group G2 may be responsible for shard S1. During the reconfiguration from 10 to 11, G1 and G2 must use RPC to move the contents of shard S1 (the key/value pairs) from G1 to G2.

- Note: Only RPC may be used for interaction among clients and servers. For example, different instances of your server are not allowed to share Go variables or files.
- Note: This lab uses "configuration" to refer to the assignment of shards to replica groups. This is not the same as Raft cluster membership changes. You don't have to implement Raft cluster membership changes.

This lab's general architecture (a configuration service and a set of replica groups) follows the same general pattern as Flat Datacenter Storage, BigTable, Spanner, FAWN, Apache HBase, Rosebud, Spinnaker, and many others. These systems differ in many details from this lab, though, and are also typically more sophisticated and capable. For example, the lab doesn't evolve the sets of peers in each Raft group; its data and query models are very simple; and handoff of shards is slow and doesn't allow concurrent client access.

- Note: Your Lab 5 sharded server, Lab 5 shard controller, and Lab 4 kvraft must all use the same Raft implementation.

### Getting Started

We supply you with skeleton code and tests in `src/shardctrler` and `src/shardkv`.

To get up and running, execute the following commands:

```sh
$ cd src/shardctrler
$ go test
--- FAIL: TestBasic (0.00s)
test_test.go:11: wanted 1 groups, got 0
FAIL
exit status 1
FAIL shardctrler 0.008s
$
```

When you're done, your implementation should pass all the tests in the `src/shardctrler` directory, and all the ones in `src/shardkv`.

### Part A: The Controller and Static Sharding ("easy")

First you'll implement the shard controller, in `shardctrler/server.go` and `client.go`, and a sharded key/value server that can handle an unchanging (static) configuration. When you're done, your code should pass all the tests in the `shardctrler/` directory, and the `5A` tests in `shardkv/`.

```sh
$ cd src/shardctrler
$ go test
Test: Basic leave/join ...
... Passed
Test: Historical queries ...
... Passed
Test: Move ...
... Passed
Test: Concurrent leave/join ...
... Passed
Test: Minimal transfers after joins ...
... Passed
Test: Minimal transfers after leaves ...
... Passed
Test: Multi-group join/leave ...
... Passed
Test: Concurrent multi leave/join ...
... Passed
Test: Minimal transfers after multijoins ...
... Passed
Test: Minimal transfers after multileaves ...
... Passed
Test: Check Same config on servers ...
... Passed
PASS
ok shardctrler 5.863s
$
$ cd ../shardkv
$ go test -run 5A
Test (5A): static shards ...
... Passed
Test (5A): rejection ...
... Passed
PASS
ok shardkv 9.262s
$
```

The shardctrler manages a sequence of numbered configurations. Each configuration describes a set of replica groups and an assignment of shards to replica groups. Whenever this assignment needs to change, the shard controller creates a new configuration with the new assignment. Key/value clients and servers contact the shardctrler when they want to know the current (or a past) configuration.

Your implementation must support the RPC interface described in `shardctrler/common.go`, which consists of `Join`, `Leave`, `Move`, and `Query` RPCs. These RPCs are intended to allow an administrator (and the tests) to control the shardctrler: to add new replica groups, to eliminate replica groups, and to move shards between replica groups.

The `Join` RPC is used by an administrator to add new replica groups. Its argument is a set of mappings from unique, non-zero replica group identifiers (GIDs) to lists of server names. The shardctrler should react by creating a new configuration that includes the new replica groups. The new configuration should divide the shards as evenly as possible among the full set of groups, and should move as few shards as possible to achieve that goal. The shardctrler should allow re-use of a GID if it's not part of the current configuration (i.e. a GID should be allowed to Join, then Leave, then Join again).

The `Leave` RPC's argument is a list of GIDs of previously joined groups. The shardctrler should create a new configuration that does not include those groups, and that assigns those groups' shards to the remaining groups. The new configuration should divide the shards as evenly as possible among the groups, and should move as few shards as possible to achieve that goal.

The `Move` RPC's arguments are a shard number and a GID. The shardctrler should create a new configuration in which the shard is assigned to the group. The purpose of `Move` is to allow us to test your software. A `Join` or `Leave` following a `Move` will likely un-do the `Move`, since `Join` and `Leave` re-balance.

The `Query` RPC's argument is a configuration number. The shardctrler replies with the configuration that has that number. If the number is -1 or bigger than the biggest known configuration number, the shardctrler should reply with the latest configuration. The result of `Query(-1)` should reflect every `Join`, `Leave`, or `Move` RPC that the shardctrler finished handling before it received the `Query(-1)` RPC.

The very first configuration should be numbered zero. It should contain no groups, and all shards should be assigned to GID zero (an invalid GID). The next configuration (created in response to a `Join` RPC) should be numbered 1, &c. There will usually be significantly more shards than groups (i.e., each group will serve more than one shard), in order that load can be shifted at a fairly fine granularity.

#### Task

You must implement the interface specified above in `client.go` and `server.go` in the `shardctrler/` directory. Your shardctrler must be fault-tolerant, using your Raft library from Lab 3/4. You have completed this task when you pass all the tests in `shardctrler/`.

#### Hints

- Start with a stripped-down copy of your kvraft server.
- You should implement duplicate client request detection for RPCs to the shard controller. The shardctrler tests don't test this, but the shardkv tests will later use your shardctrler on an unreliable network; you may have trouble passing the shardkv tests if your shardctrler doesn't filter out duplicate RPCs.
- The code in your state machine that performs the shard rebalancing needs to be deterministic. In Go, map iteration order is not deterministic.
- Go maps are references. If you assign one variable of type map to another, both variables refer to the same map. Thus if you want to create a new `Config` based on a previous one, you need to create a new map object (with `make()`) and copy the keys and values individually.
- The Go race detector (go test -race) may help you find bugs.

Next, in the `shardkv/` directory, implement enough of a sharded key/value server to pass the first two tests in `shardkv/`. Again, start by copying code from your existing `kvraft` server. You should be able to get the first test to pass without doing anything special regarding sharding, since the `shardkv/client.go` we give you takes care of sending RPCs to the group that the controller assigns to the key in question.

For the second `shardkv` test, each k/v replica group must reject requests for keys for shards for which the group is not the assigned group. At this point, it's enough for the k/v servers to periodically ask the controller for the latest configuration, and to check that configuration each time a client Get/Put/Append RPC arrives. Use `key2shard()` (in `client.go`) to find the shard number for a key.

Your server should respond with an `ErrWrongGroup` error to a client RPC with a key that the server isn't responsible for (i.e. for a key whose shard is not assigned to the server's group).

Your server should not call the shard controller's `Join()` handler. The tester will call `Join()` when appropriate.

### Part B: Shard Movement ("hard")

The main task in this part of the lab is to move shards among replica groups when the controller changes the sharding, and do it in a way that provides linearizable k/v client operations.

Each of your shards is only required to make progress when a majority of servers in the shard's Raft replica group is alive and can talk to each other, and can talk to a majority of the `shardctrler` servers. Your implementation must operate (serve requests and be able to re-configure as needed) even if a minority of servers in some replica group(s) are dead, temporarily unavailable, or slow.

A shardkv server is a member of only a single replica group. The set of servers in a given replica group will never change.

We supply you with `client.go` code that sends each RPC to the replica group responsible for the RPC's key. It re-tries if the replica group says it is not responsible for the key; in that case, the client code asks the shard controller for the latest configuration and tries again. You'll have to modify client.go as part of your support for dealing with duplicate client RPCs, much as in the kvraft lab.

When you're done your code should pass all the shardkv tests other than the challenge tests:

```sh
$ cd src/shardkv
$ go test
Test (5A): static shards ...
... Passed
Test (5A): rejection ...
... Passed
Test (5B): join then leave ...
... Passed
Test (5B): snapshots, join, and leave ...
labgob warning: Decoding into a non-default variable/field Num may not work
... Passed
Test (5B): servers miss configuration changes...
... Passed
Test (5B): concurrent puts and configuration changes...
... Passed
Test (5B): more concurrent puts and configuration changes...
... Passed
Test (5B): concurrent configuration change and restart...
... Passed
Test (5B): unreliable 1...
... Passed
Test (5B): unreliable 2...
... Passed
Test (5B): unreliable 3...
... Passed
Test: shard deletion (challenge 1) ...
... Passed
Test: unaffected shard access (challenge 2) ...
... Passed
Test: partial migration shard access (challenge 2) ...
... Passed
PASS
ok shardkv 173.974s
$
```

You will need to make your servers watch for configuration changes, and when one is detected, to start the shard migration process. If a replica group loses a shard, it must stop serving requests to keys in that shard immediately, and start migrating the data for that shard to the replica group that is taking over ownership. If a replica group gains a shard, it needs to wait for the previous owner to send over the old shard data before accepting requests for that shard.

#### Task

Implement shard migration during configuration changes. Make sure that all servers in a replica group do the migration at the same point in the sequence of operations they execute, so that they all either accept or reject concurrent client requests. You should focus on passing the second test ("join then leave") before working on the later tests. You are done with this task when you pass all tests up to, but not including, `TestDelete`.

- Note: Your server will need to periodically poll the shardctrler to learn about new configurations. The tests expect that your code polls roughly every 100 milliseconds; more often is OK, but much less often may cause problems.

- Note: Servers will need to send RPCs to each other in order to transfer shards during configuration changes. The shardctrler's `Config` struct contains server names, but you need a `labrpc.ClientEnd` in order to send an RPC. You should use the `make_end()` function passed to `StartServer()` to turn a server name into a `ClientEnd`. `shardkv/client.go` contains code that does this.

#### Hints

- Process re-configurations one at a time, in order.
- If a test fails, check for gob errors (e.g. "gob: type not registered for interface ..."). Go doesn't consider gob errors to be fatal, although they are fatal for the lab.
- You'll need to provide at-most-once semantics (duplicate detection) for client requests across shard movement.
- Think about how the shardkv client and server should deal with `ErrWrongGroup`. Should the client change the sequence number if it receives `ErrWrongGroup`? Should the server update the client state if it returns `ErrWrongGroup` when executing a `Get`/`Put` request?
- After a server has moved to a new configuration, it is acceptable for it to continue to store shards that it no longer owns (though this would be regrettable in a real system). This may help simplify your server implementation.
- When group G1 needs a shard from G2 during a configuration change, does it matter at what point during its processing of log entries G2 sends the shard to G1?
- You can send an entire map in an RPC request or reply, which may help keep the code for shard transfer simple.
- If one of your RPC handlers includes in its reply a map (e.g. a key/value map) that's part of your server's state, you may get bugs due to races. The RPC system has to read the map in order to send it to the caller, but it isn't holding a lock that covers the map. Your server, however, may proceed to modify the same map while the RPC system is reading it. The solution is for the RPC handler to include a copy of the map in the reply.
- If you put a map or a slice in a Raft log entry, and your key/value server subsequently sees the entry on the `applyCh` and saves a reference to the map/slice in your key/value server's state, you may have a race. Make a copy of the map/slice, and store the copy in your key/value server's state. The race is between your key/value server modifying the map/slice and Raft reading it while persisting its log.
- During a configuration change, a pair of groups may need to move shards in both directions between them. If you see deadlock, this is a possible source.

### No-credit challenge exercises

These two features would be essential if you were to build a system like this for production use.

#### Garbage collection of state

When a replica group loses ownership of a shard, that replica group should eliminate the keys that it lost from its database. It is wasteful for it to keep values that it no longer owns, and no longer serves requests for. However, this poses some issues for migration. Say we have two groups, G1 and G2, and there is a new configuration C that moves shard S from G1 to G2. If G1 erases all keys in S from its database when it transitions to C, how does G2 get the data for S when it tries to move to C?

##### Challenge

Cause each replica group to keep old shards no longer than absolutely necessary. Your solution must work even if all the servers in a replica group like G1 above crash and are then brought back up. You have completed this challenge if you pass `TestChallenge1Delete`.

#### Client requests during configuration changes

The simplest way to handle configuration changes is to disallow all client operations until the transition has completed. While conceptually simple, this approach is not feasible in production-level systems; it results in long pauses for all clients whenever machines are brought in or taken out. It would be better to continue serving shards that are not affected by the ongoing configuration change.

##### Challenge

Modify your solution so that client operations for keys in unaffected shards continue to execute during a configuration change. You have completed this challenge when you pass `TestChallenge2Unaffected`.

While the optimization above is good, we can still do better. Say that some replica group G3, when transitioning to C, needs shard S1 from G1, and shard S2 from G2. We really want G3 to immediately start serving a shard once it has received the necessary state, even if it is still waiting for some other shards. For example, if G1 is down, G3 should still start serving requests for S2 once it receives the appropriate data from G2, despite the transition to C not yet having completed.

##### Challenge

Modify your solution so that replica groups start serving shards the moment they are able to, even if a configuration is still ongoing. You have completed this challenge when you pass `TestChallenge2Partial`.

### Handin procedure

Before submitting, please run _all_ the tests one final time.

Also, note that your Lab 5 sharded server, Lab 5 shard controller, and Lab 4 kvraft must all use the same Raft implementation.

Before submitting, double check that your solution works with:

```sh
$ go test ./raft
$ go test ./kvraft
$ go test ./shardctrler
$ go test ./shardkv
```

## Files Agent Should Modify

The agent should implement the solution by modifying the following files:

- `src/shardctrler/client.go`
- `src/shardctrler/common.go`
- `src/shardctrler/server.go`
- `src/shardkv/client.go`
- `src/shardkv/common.go`
- `src/shardkv/server.go`

**Important**: Do not modify test files, configuration files, or other infrastructure files.
