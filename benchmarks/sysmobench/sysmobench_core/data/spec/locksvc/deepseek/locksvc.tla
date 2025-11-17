---- MODULE locksvc ----
EXTENDS Naturals, Sequences, FiniteSets, TLC
CONSTANTS NumClients, LockMsgType, UnlockMsgType, GrantMsgType
ASSUME NumClients \in Nat \ {0}
ASSUME {LockMsgType, UnlockMsgType, GrantMsgType} \subseteq Nat
ASSUME LockMsgType # UnlockMsgType /\ LockMsgType # GrantMsgType /\ UnlockMsgType # GrantMsgType
Server == 0
Clients == 1..NumClients
Nodes == {Server} \cup Clients
MessageSet == { [from |-> c, type |-> LockMsgType] : c \in Clients } \cup { [from |-> c, type |-> UnlockMsgType] : c \in Clients } \cup {GrantMsgType}
VARIABLES hasLock, queue, network
vars == << hasLock, queue, network >>
Init == 
    hasLock = [c \in Clients |-> FALSE] /\
    queue = << >> /\
    network = [n \in Nodes |-> {} ]
SendLock(c) == 
    /\ c \in Clients
    /\ hasLock[c] = FALSE
    /\ [from |-> c, type |-> LockMsgType] \notin network[Server]
    /\ network' = [network EXCEPT ![Server] = network[Server] \cup {[from |-> c, type |-> LockMsgType]} ]
    /\ UNCHANGED << hasLock, queue >>
SendUnlock(c) == 
    /\ c \in Clients
    /\ hasLock[c] = TRUE
    /\ network' = [network EXCEPT ![Server] = network[Server] \cup {[from |-> c, type |-> UnlockMsgType]} ]
    /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
    /\ UNCHANGED queue
ProcessServerMessage(m) == 
    /\ m \in network[Server]
    /\ \/ /\ m.type = LockMsgType
          /\ IF queue = << >> 
             THEN /\ network' = [network EXCEPT ![m.from] = network[m.from] \cup {GrantMsgType}, ![Server] = network[Server] \ {m} ]
                  /\ queue' = queue
             ELSE /\ queue' = Append(queue, m.from)
                  /\ network' = [network EXCEPT ![Server] = network[Server] \ {m} ]
       \/ /\ m.type = UnlockMsgType
          /\ IF queue = << >> 
             THEN /\ queue' = queue
                  /\ network' = [network EXCEPT ![Server] = network[Server] \ {m} ]
             ELSE /\ LET newQueue == Tail(queue) IN
                    queue' = newQueue
                    /\ IF newQueue # << >> 
                       THEN network' = [network EXCEPT ![Head(newQueue)] = network[Head(newQueue)] \cup {GrantMsgType}, ![Server] = network[Server] \ {m} ]
                       ELSE network' = [network EXCEPT ![Server] = network[Server] \ {m} ]
    /\ UNCHANGED hasLock
ClientReceiveGrant(c) == 
    /\ c \in Clients
    /\ GrantMsgType \in network[c]
    /\ network' = [network EXCEPT ![c] = network[c] \ {GrantMsgType} ]
    /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
    /\ UNCHANGED queue
Next == 
    \/ \E c \in Clients : SendLock(c)
    \/ \E c \in Clients : SendUnlock(c)
    \/ \E m \in network[Server] : ProcessServerMessage(m)
    \/ \E c \in Clients : ClientReceiveGrant(c)
ServerProcessAction == \E m \in network[Server] : ProcessServerMessage(m)
ClientReceiveAction == \E c \in Clients : ClientReceiveGrant(c)
Spec == Init /\ [][Next]_vars 
          /\ \A c \in Clients : WF_vars(SendLock(c))
          /\ \A d \in Clients : WF_vars(SendUnlock(d))
          /\ WF_vars(ServerProcessAction)
          /\ WF_vars(ClientReceiveAction)
====