---- MODULE locksvc ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANT NumClients

Client == 1..NumClients
Server == 0
Node == Client \cup {Server}

Lock(c) == [type |-> "Lock", from |-> c]
Unlock(c) == [type |-> "Unlock", from |-> c]
Grant(c) == [type |-> "Grant", to |-> c]
Message == { Lock(c) : c \in Client } \cup { Unlock(c) : c \in Client } \cup { Grant(c) : c \in Client }

EmptyMsgBag == [m \in Message |-> 0] \* renamed to avoid conflict with Bags.EmptyBag
InBag(b, x) == b[x] > 0
AddBag(b, x) == [b EXCEPT ![x] = @ + 1]
RemBag(b, x) == [b EXCEPT ![x] = @ - 1]

Phases == {"idle", "waitingForGrant", "critical", "releasing"}

SeqContains(s, x) == \E i \in 1..Len(s) : s[i] = x

VARIABLES
  q,           \* sequence of clients (FIFO); head holds/next to hold
  hasLock,     \* [Client -> BOOLEAN]
  clientPhase, \* [Client -> Phases]
  Mailbox      \* [Node -> [Message -> Nat]]

vars == << q, hasLock, clientPhase, Mailbox >>

TypeOK ==
  /\ q \in Seq(Client)
  /\ hasLock \in [Client -> BOOLEAN]
  /\ clientPhase \in [Client -> Phases]
  /\ Mailbox \in [Node -> [Message -> Nat]]

Init ==
  /\ q = << >>
  /\ hasLock = [c \in Client |-> FALSE]
  /\ clientPhase = [c \in Client |-> "idle"]
  /\ Mailbox = [n \in Node |-> EmptyMsgBag]
  /\ TypeOK \* minimal fix: place TypeOK after concrete assignments to avoid enumerating infinite sets during Init

ClientSendLock(c) ==
  /\ c \in Client
  /\ clientPhase[c] = "idle"
  /\ hasLock[c] = FALSE
  /\ Mailbox' = [Mailbox EXCEPT ![Server] = AddBag(@, Lock(c))]
  /\ clientPhase' = [clientPhase EXCEPT ![c] = "waitingForGrant"]
  /\ UNCHANGED << q, hasLock >>

ClientRecvGrant(c) ==
  /\ c \in Client
  /\ clientPhase[c] = "waitingForGrant"
  /\ InBag(Mailbox[c], Grant(c))
  /\ Mailbox' = [Mailbox EXCEPT ![c] = RemBag(@, Grant(c))]
  /\ hasLock' = [hasLock EXCEPT ![c] = TRUE]
  /\ clientPhase' = [clientPhase EXCEPT ![c] = "critical"]
  /\ UNCHANGED q

ClientSendUnlock(c) ==
  /\ c \in Client
  /\ clientPhase[c] = "critical"
  /\ hasLock[c] = TRUE
  /\ Mailbox' = [Mailbox EXCEPT ![Server] = AddBag(@, Unlock(c))]
  /\ hasLock' = [hasLock EXCEPT ![c] = FALSE]
  /\ clientPhase' = [clientPhase EXCEPT ![c] = "releasing"]
  /\ UNCHANGED q

ClientUnlockProcessed(c) ==
  /\ c \in Client
  /\ clientPhase[c] = "releasing"
  /\ ~SeqContains(q, c)
  /\ clientPhase' = [clientPhase EXCEPT ![c] = "idle"]
  /\ UNCHANGED << q, hasLock, Mailbox >>

ServerStep ==
  \/ \E c \in Client :
       /\ InBag(Mailbox[Server], Lock(c))
       /\ q' = Append(q, c)
       /\ Mailbox' =
            [Mailbox EXCEPT
              ![Server] = RemBag(@, Lock(c)),
              ![c] = IF Len(q) = 0 THEN AddBag(@, Grant(c)) ELSE @]
       /\ UNCHANGED << hasLock, clientPhase >>
  \/ \E c \in Client :
       /\ InBag(Mailbox[Server], Unlock(c))
       /\ LET qNew == Tail(q) IN
            /\ q' = qNew
            /\ Mailbox' =
                 IF qNew = << >> THEN
                   [Mailbox EXCEPT
                      ![Server] = RemBag(@, Unlock(c))]
                 ELSE
                   [Mailbox EXCEPT
                      ![Server] = RemBag(@, Unlock(c)),
                      ![Head(qNew)] = AddBag(@, Grant(Head(qNew)))]
       /\ UNCHANGED << hasLock, clientPhase >>

Next ==
  \/ \E c \in Client : ClientSendLock(c)
  \/ \E c \in Client : ClientRecvGrant(c)
  \/ \E c \in Client : ClientSendUnlock(c)
  \/ \E c \in Client : ClientUnlockProcessed(c)
  \/ ServerStep

Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(ServerStep)
  /\ \A c \in Client :
       WF_vars(ClientRecvGrant(c))
       /\ WF_vars(ClientSendUnlock(c))
       /\ WF_vars(ClientUnlockProcessed(c))

====