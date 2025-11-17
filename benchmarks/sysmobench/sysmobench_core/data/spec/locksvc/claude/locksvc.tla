---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NumClients

VARIABLES 
    network,
    queue,
    hasLock,
    pc

vars == <<network, queue, hasLock, pc>>

ServerID == 0
ClientSet == 1..NumClients
NodeSet == {ServerID} \cup ClientSet

LockMsg == 1
UnlockMsg == 2
GrantMsg == 3

TypeOK ==
    /\ network \in [NodeSet -> Seq(Nat \cup [from: NodeSet, type: {LockMsg, UnlockMsg}])]
    /\ queue \in Seq(ClientSet)
    /\ hasLock \in [ClientSet -> BOOLEAN]
    /\ pc \in [NodeSet -> STRING]

Init == 
    /\ network = [n \in NodeSet |-> <<>>]
    /\ queue = <<>>
    /\ hasLock = [c \in ClientSet |-> FALSE]
    /\ pc = [n \in NodeSet |-> IF n = ServerID THEN "serverLoop" ELSE "acquireLock"]

RequestLock(client) ==
    /\ pc[client] = "acquireLock"
    /\ network' = [network EXCEPT ![ServerID] = Append(@, [from |-> client, type |-> LockMsg])]
    /\ pc' = [pc EXCEPT ![client] = "waitingForGrant"]
    /\ UNCHANGED <<queue, hasLock>>

ProcessLockMsg(server) ==
    /\ pc[server] = "serverLoop"
    /\ server = ServerID
    /\ Len(network[server]) > 0
    /\ LET msg == Head(network[server])
       IN /\ msg.type = LockMsg
          /\ IF queue = <<>>
             THEN /\ network' = [network EXCEPT ![server] = Tail(@), ![msg.from] = Append(@, GrantMsg)]
                  /\ queue' = Append(queue, msg.from)
             ELSE /\ network' = [network EXCEPT ![server] = Tail(@)]
                  /\ queue' = Append(queue, msg.from)
          /\ UNCHANGED <<hasLock, pc>>

ProcessUnlockMsg(server) ==
    /\ pc[server] = "serverLoop"
    /\ server = ServerID
    /\ Len(network[server]) > 0
    /\ LET msg == Head(network[server])
       IN /\ msg.type = UnlockMsg
          /\ network' = [network EXCEPT ![server] = Tail(@)]
          /\ queue' = Tail(queue)
          /\ IF queue' # <<>>
             THEN network' = [network' EXCEPT ![Head(queue')] = Append(@, GrantMsg)]
             ELSE TRUE
          /\ UNCHANGED <<hasLock, pc>>

ReceiveGrant(client) ==
    /\ pc[client] = "waitingForGrant"
    /\ Len(network[client]) > 0
    /\ Head(network[client]) = GrantMsg
    /\ network' = [network EXCEPT ![client] = Tail(@)]
    /\ hasLock' = [hasLock EXCEPT ![client] = TRUE]
    /\ pc' = [pc EXCEPT ![client] = "criticalSection"]
    /\ UNCHANGED queue

ReleaseLock(client) ==
    /\ pc[client] = "criticalSection"
    /\ hasLock[client] = TRUE
    /\ network' = [network EXCEPT ![ServerID] = Append(@, [from |-> client, type |-> UnlockMsg])]
    /\ hasLock' = [hasLock EXCEPT ![client] = FALSE]
    /\ pc' = [pc EXCEPT ![client] = "done"]
    /\ UNCHANGED queue

Next == 
    \/ \E client \in ClientSet : RequestLock(client)
    \/ ProcessLockMsg(ServerID)
    \/ ProcessUnlockMsg(ServerID)
    \/ \E client \in ClientSet : ReceiveGrant(client)
    \/ \E client \in ClientSet : ReleaseLock(client)
    \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(\E client \in ClientSet : ReleaseLock(client))

====