---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    NumServers,
    NumClients,
    Keys,
    Values

Servers == 1..NumServers
Clients == 1..NumClients
Nodes == Servers \cup Clients

Nil == 0

StateFollower == "follower"
StateCandidate == "candidate"
StateLeader == "leader"

Put == "put"
Get == "get"

RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

MsgType == {RequestVoteRequest, RequestVoteResponse, AppendEntriesRequest, AppendEntriesResponse, ClientPutRequest, ClientPutResponse, ClientGetRequest, ClientGetResponse}

Cmd == [type: {Put, Get}, key: Keys, value: Values \cup {Nil}, idx: Nat]
Entry == [term: Nat, cmd: Cmd, client: Clients]
Response == [idx: Nat, key: Keys, value: Values \cup {Nil}, ok: BOOLEAN]

Msg ==
    [ type: MsgType,
      term: Nat,
      source: Nodes,
      dest: Nodes,
      lastLogTerm: Nat,
      lastLogIndex: Nat,
      voteGranted: BOOLEAN,
      prevLogIndex: Nat,
      prevLogTerm: Nat,
      entries: Seq(Entry),
      commitIndex: Nat,
      success: BOOLEAN,
      matchIndex: Nat,
      cmd: Cmd \cup {Nil},
      response: Response \cup {Nil},
      leaderHint: Servers \cup {Nil}
    ]

VARIABLES
    state,
    currentTerm,
    votedFor,
    leaderVar,
    logVar,
    commitIndex,
    lastApplied,
    nextIndex,
    matchIndex,
    votesResponded,
    votesGranted,
    Timeout,
    KV,
    KVDomain,
    ClLeader,
    ClientReqIdx,
    Network

vars == << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx, Network >>

IsQuorum(S) == 2 * Cardinality(S) > NumServers

LastLogTerm(l) == IF Len(l) = 0 THEN 0 ELSE l[Len(l)].term

LogUpToDate(lt, li, lj) ==
    lt > LastLogTerm(lj) \/
    /\ lt = LastLogTerm(lj)
       /\ li >= Len(lj)

MaxSet(S) == CHOOSE m \in S: \A x \in S: x <= m

AgreeSet(i, k) == {i} \cup { j \in Servers: matchIndex[i][j] >= k }

MaxAgreeIndex(i) ==
    LET L == logVar[i] IN
    LET Ks == { k \in 1..Len(L) :
                 IsQuorum(AgreeSet(i, k)) /\ L[k].term = currentTerm[i] } IN
    IF Ks # {} THEN MaxSet(Ks) ELSE 0

MaxTerm == NumServers
MaxClientReq == NumClients

Init ==
    /\ state = [i \in Servers |-> StateFollower]
    /\ currentTerm = [i \in Servers |-> 0]
    /\ votedFor = [i \in Servers |-> Nil]
    /\ leaderVar = [i \in Servers |-> Nil]
    /\ logVar = [i \in Servers |-> << >>]
    /\ commitIndex = [i \in Servers |-> 0]
    /\ lastApplied = [i \in Servers |-> 0]
    /\ nextIndex = [i \in Servers |-> [j \in Servers |-> 1]]
    /\ matchIndex = [i \in Servers |-> [j \in Servers |-> 0]]
    /\ votesResponded = [i \in Servers |-> {}]
    /\ votesGranted = [i \in Servers |-> {}]
    /\ Timeout = [i \in Servers |-> FALSE]
    /\ KV = [i \in Servers |-> [k \in Keys |-> CHOOSE v \in Values: TRUE]]
    /\ KVDomain = [i \in Servers |-> {}]
    /\ ClLeader = [c \in Clients |-> Nil]
    /\ ClientReqIdx = [c \in Clients |-> 0]
    /\ Network = {}

LeaderTimeout(i) ==
    /\ i \in Servers
    /\ Timeout[i]
    /\ state[i] \in {StateFollower, StateCandidate}
    /\ currentTerm[i] < MaxTerm
    /\ state' = [state EXCEPT ![i] = StateCandidate]
    /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
    /\ votedFor' = [votedFor EXCEPT ![i] = i]
    /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
    /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
    /\ leaderVar' = [leaderVar EXCEPT ![i] = Nil]
    /\ Timeout' = [Timeout EXCEPT ![i] = FALSE]
    /\ UNCHANGED << logVar, commitIndex, lastApplied, nextIndex, matchIndex, KV, KVDomain, ClLeader, ClientReqIdx, Network >>

Tick(i) ==
    /\ i \in Servers
    /\ Timeout' = [Timeout EXCEPT ![i] = TRUE]
    /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, KV, KVDomain, ClLeader, ClientReqIdx, Network >>

SendRVQ(i, j) ==
    /\ i \in Servers /\ j \in Servers /\ i # j
    /\ state[i] = StateCandidate
    /\ LET m ==
         [ type |-> RequestVoteRequest,
           term |-> currentTerm[i],
           source |-> i, dest |-> j,
           lastLogTerm |-> LastLogTerm(logVar[i]),
           lastLogIndex |-> Len(logVar[i]),
           voteGranted |-> FALSE,
           prevLogIndex |-> 0, prevLogTerm |-> 0,
           entries |-> << >>,
           commitIndex |-> 0,
           success |-> FALSE,
           matchIndex |-> 0,
           cmd |-> Nil,
           response |-> Nil,
           leaderHint |-> Nil ] IN
       Network' = Network \cup {m}
    /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>

DeliverRVQ ==
    \E m \in Network:
      /\ m.type = RequestVoteRequest
      /\ m.dest \in Servers
      /\ LET j == m.dest IN
         LET stepDown ==
               m.term > currentTerm[j] IN
         LET newTerm == IF stepDown THEN m.term ELSE currentTerm[j] IN
         LET st1 == IF stepDown THEN StateFollower ELSE state[j] IN
         LET vf1 == IF stepDown THEN Nil ELSE votedFor[j] IN
         LET ld1 == IF stepDown THEN Nil ELSE leaderVar[j] IN
         LET grant ==
               /\ m.term = newTerm
               /\ vf1 \in {Nil, m.source}
               /\ LogUpToDate(m.lastLogTerm, m.lastLogIndex, logVar[j]) IN
         LET vf2 == IF grant THEN m.source ELSE vf1 IN
         LET reply ==
           [ type |-> RequestVoteResponse,
             term |-> newTerm,
             source |-> j, dest |-> m.source,
             lastLogTerm |-> 0, lastLogIndex |-> 0,
             voteGranted |-> grant,
             prevLogIndex |-> 0, prevLogTerm |-> 0,
             entries |-> << >>,
             commitIndex |-> 0,
             success |-> FALSE,
             matchIndex |-> 0,
             cmd |-> Nil,
             response |-> Nil,
             leaderHint |-> Nil ] IN
         /\ state' = [state EXCEPT ![j] = st1]
         /\ currentTerm' = [currentTerm EXCEPT ![j] = newTerm]
         /\ votedFor' = [votedFor EXCEPT ![j] = vf2]
         /\ leaderVar' = [leaderVar EXCEPT ![j] = ld1]
         /\ Network' = (Network \ {m}) \cup {reply}
         /\ UNCHANGED << logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>

DeliverRVP ==
    \E m \in Network:
      /\ m.type = RequestVoteResponse
      /\ m.dest \in Servers
      /\ LET i == m.dest IN
         IF m.term > currentTerm[i] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
           /\ state' = [state EXCEPT ![i] = StateFollower]
           /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
           /\ leaderVar' = [leaderVar EXCEPT ![i] = Nil]
           /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
           /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
           /\ Network' = Network \ {m}
           /\ UNCHANGED << logVar, commitIndex, lastApplied, nextIndex, matchIndex, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>
         ELSE IF m.term < currentTerm[i] \/ state[i] # StateCandidate THEN
           /\ Network' = Network \ {m}
           /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>
         ELSE
           LET vr1 == votesResponded[i] \cup {m.source} IN
           LET vg1 == IF m.voteGranted THEN votesGranted[i] \cup {m.source} ELSE votesGranted[i] IN
           LET becomeLeader == IsQuorum(vg1) IN
           /\ votesResponded' = [votesResponded EXCEPT ![i] = vr1]
           /\ votesGranted' = [votesGranted EXCEPT ![i] = vg1]
           /\ Timeout' = [Timeout EXCEPT ![i] = IF m.voteGranted THEN FALSE ELSE @]
           /\ state' = [state EXCEPT ![i] = IF becomeLeader THEN StateLeader ELSE @]
           /\ nextIndex' = [nextIndex EXCEPT
                              ![i] = IF becomeLeader THEN [j \in Servers |-> Len(logVar[i]) + 1] ELSE @]
           /\ matchIndex' = [matchIndex EXCEPT
                              ![i] = IF becomeLeader THEN [j \in Servers |-> 0] ELSE @]
           /\ leaderVar' = [leaderVar EXCEPT ![i] = IF becomeLeader THEN i ELSE @]
           /\ Network' = Network \ {m}
           /\ UNCHANGED << currentTerm, votedFor, logVar, commitIndex, lastApplied, KV, KVDomain, ClLeader, ClientReqIdx >>

SendAE(i, j) ==
    /\ i \in Servers /\ j \in Servers /\ i # j
    /\ state[i] = StateLeader
    /\ LET ni == nextIndex[i][j] IN
       LET prevIdx == (IF ni > 0 THEN ni - 1 ELSE 0) IN
       LET prevTerm ==
            IF prevIdx = 0 THEN 0 ELSE logVar[i][prevIdx].term IN
       LET entries == SubSeq(logVar[i], ni, Len(logVar[i])) IN
       LET m ==
         [ type |-> AppendEntriesRequest,
           term |-> currentTerm[i],
           source |-> i, dest |-> j,
           lastLogTerm |-> 0, lastLogIndex |-> 0,
           voteGranted |-> FALSE,
           prevLogIndex |-> prevIdx, prevLogTerm |-> prevTerm,
           entries |-> entries,
           commitIndex |-> commitIndex[i],
           success |-> FALSE,
           matchIndex |-> 0,
           cmd |-> Nil,
           response |-> Nil,
           leaderHint |-> Nil ] IN
       Network' = Network \cup {m}
    /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>

DeliverAEQ ==
    \E m \in Network:
      /\ m.type = AppendEntriesRequest
      /\ m.dest \in Servers
      /\ LET j == m.dest IN
         LET stepDown == m.term > currentTerm[j] IN
         LET newTerm == IF stepDown THEN m.term ELSE currentTerm[j] IN
         LET st1 == IF stepDown THEN StateFollower ELSE state[j] IN
         LET vf1 == IF stepDown THEN Nil ELSE votedFor[j] IN
         LET logOK ==
              (m.prevLogIndex = 0)
              \/ ( /\ m.prevLogIndex <= Len(logVar[j])
                   /\ logVar[j][m.prevLogIndex].term = m.prevLogTerm ) IN
         LET st2 == IF /\ m.term = newTerm /\ st1 = StateCandidate THEN StateFollower ELSE st1 IN
         LET leader2 == IF m.term = newTerm THEN m.source ELSE leaderVar[j] IN
         LET Timeout2 == IF m.term = newTerm THEN FALSE ELSE Timeout[j] IN
         IF m.term < newTerm THEN
           LET reply ==
             [ type |-> AppendEntriesResponse,
               term |-> newTerm,
               source |-> j, dest |-> m.source,
               lastLogTerm |-> 0, lastLogIndex |-> 0,
               voteGranted |-> FALSE,
               prevLogIndex |-> 0, prevLogTerm |-> 0,
               entries |-> << >>,
               commitIndex |-> 0,
               success |-> FALSE,
               matchIndex |-> 0,
               cmd |-> Nil,
               response |-> Nil,
               leaderHint |-> Nil ] IN
           /\ currentTerm' = [currentTerm EXCEPT ![j] = newTerm]
           /\ state' = [state EXCEPT ![j] = st1]
           /\ votedFor' = [votedFor EXCEPT ![j] = vf1]
           /\ leaderVar' = [leaderVar EXCEPT ![j] = leaderVar[j]]
           /\ Timeout' = Timeout
           /\ Network' = (Network \ {m}) \cup {reply}
           /\ UNCHANGED << logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, KV, KVDomain, ClLeader, ClientReqIdx >>
         ELSE
           IF ~logOK \/ m.term # newTerm THEN
             LET reply ==
               [ type |-> AppendEntriesResponse,
                 term |-> newTerm,
                 source |-> j, dest |-> m.source,
                 lastLogTerm |-> 0, lastLogIndex |-> 0,
                 voteGranted |-> FALSE,
                 prevLogIndex |-> 0, prevLogTerm |-> 0,
                 entries |-> << >>,
                 commitIndex |-> 0,
                 success |-> FALSE,
                 matchIndex |-> 0,
                 cmd |-> Nil,
                 response |-> Nil,
                 leaderHint |-> Nil ] IN
             /\ currentTerm' = [currentTerm EXCEPT ![j] = newTerm]
             /\ state' = [state EXCEPT ![j] = st2]
             /\ votedFor' = [votedFor EXCEPT ![j] = vf1]
             /\ leaderVar' = [leaderVar EXCEPT ![j] = leader2]
             /\ Timeout' = [Timeout EXCEPT ![j] = Timeout2]
             /\ Network' = (Network \ {m}) \cup {reply}
             /\ UNCHANGED << logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, KV, KVDomain, ClLeader, ClientReqIdx >>
           ELSE
             LET prefix == IF m.prevLogIndex = 0 THEN << >> ELSE SubSeq(logVar[j], 1, m.prevLogIndex) IN
             LET newLog == prefix \o m.entries IN
             LET newCommit == IF m.commitIndex <= Len(newLog) THEN m.commitIndex ELSE Len(newLog) IN
             LET reply ==
               [ type |-> AppendEntriesResponse,
                 term |-> newTerm,
                 source |-> j, dest |-> m.source,
                 lastLogTerm |-> 0, lastLogIndex |-> 0,
                 voteGranted |-> FALSE,
                 prevLogIndex |-> 0, prevLogTerm |-> 0,
                 entries |-> << >>,
                 commitIndex |-> 0,
                 success |-> TRUE,
                 matchIndex |-> m.prevLogIndex + Len(m.entries),
                 cmd |-> Nil,
                 response |-> Nil,
                 leaderHint |-> Nil ] IN
             /\ currentTerm' = [currentTerm EXCEPT ![j] = newTerm]
             /\ state' = [state EXCEPT ![j] = st2]
             /\ votedFor' = [votedFor EXCEPT ![j] = vf1]
             /\ leaderVar' = [leaderVar EXCEPT ![j] = leader2]
             /\ Timeout' = [Timeout EXCEPT ![j] = Timeout2]
             /\ logVar' = [logVar EXCEPT ![j] = newLog]
             /\ commitIndex' = [commitIndex EXCEPT ![j] = MaxSet({commitIndex[j], newCommit})]
             /\ Network' = (Network \ {m}) \cup {reply}
             /\ UNCHANGED << lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, KV, KVDomain, ClLeader, ClientReqIdx >>

DeliverAEP ==
    \E m \in Network:
      /\ m.type = AppendEntriesResponse
      /\ m.dest \in Servers
      /\ LET i == m.dest IN
         IF m.term > currentTerm[i] THEN
           /\ currentTerm' = [currentTerm EXCEPT ![i] = m.term]
           /\ state' = [state EXCEPT ![i] = StateFollower]
           /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
           /\ leaderVar' = [leaderVar EXCEPT ![i] = Nil]
           /\ votesResponded' = [votesResponded EXCEPT ![i] = {}]
           /\ votesGranted' = [votesGranted EXCEPT ![i] = {}]
           /\ Network' = Network \ {m}
           /\ UNCHANGED << logVar, commitIndex, lastApplied, nextIndex, matchIndex, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>
         ELSE IF m.term < currentTerm[i] THEN
           /\ Network' = Network \ {m}
           /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>
         ELSE
           LET j == m.source IN
           /\ Timeout' = [Timeout EXCEPT ![i] = FALSE]
           /\ nextIndex' =
               [nextIndex EXCEPT
                 ![i][j] = IF m.success THEN m.matchIndex + 1
                           ELSE IF nextIndex[i][j] > 1 THEN nextIndex[i][j] - 1 ELSE 1]
           /\ matchIndex' =
               [matchIndex EXCEPT
                 ![i][j] = IF m.success THEN m.matchIndex ELSE @]
           /\ Network' = Network \ {m}
           /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, votesResponded, votesGranted, KV, KVDomain, ClLeader, ClientReqIdx >>

AdvanceCommit(i) ==
    /\ i \in Servers
    /\ state[i] = StateLeader
    /\ LET k == MaxAgreeIndex(i) IN
       commitIndex' = [commitIndex EXCEPT ![i] = MaxSet({commitIndex[i], k})]
    /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx, Network >>

ApplyCommitted(i) ==
    /\ i \in Servers
    /\ lastApplied[i] < commitIndex[i]
    /\ LET k == lastApplied[i] + 1 IN
       LET e == logVar[i][k] IN
       LET c == e.cmd IN
       LET isPut == c.type = Put IN
       LET isGet == c.type = Get IN
       LET okGet == c.key \in KVDomain[i] IN
       LET valGet == KV[i][c.key] IN
       /\ lastApplied' = [lastApplied EXCEPT ![i] = k]
       /\ KV' = [KV EXCEPT ![i] = IF isPut THEN [@ EXCEPT ![c.key] = c.value] ELSE @]
       /\ KVDomain' = [KVDomain EXCEPT ![i] = IF isPut THEN KVDomain[i] \cup {c.key} ELSE @]
       /\ Network' =
            IF state[i] = StateLeader THEN
              Network \cup {
                [ type |-> IF isPut THEN ClientPutResponse ELSE ClientGetResponse,
                  term |-> currentTerm[i],
                  source |-> i, dest |-> e.client,
                  lastLogTerm |-> 0, lastLogIndex |-> 0,
                  voteGranted |-> FALSE,
                  prevLogIndex |-> 0, prevLogTerm |-> 0,
                  entries |-> << >>,
                  commitIndex |-> 0,
                  success |-> TRUE,
                  matchIndex |-> 0,
                  cmd |-> Nil,
                  response |-> [idx |-> c.idx, key |-> c.key, value |-> IF isGet /\ okGet THEN valGet ELSE Nil, ok |-> IF isGet THEN okGet ELSE TRUE],
                  leaderHint |-> i ] }
            ELSE Network
       /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, ClLeader, ClientReqIdx >>

DeliverClientReq ==
    \E m \in Network:
      /\ m.dest \in Servers
      /\ m.type \in {ClientPutRequest, ClientGetRequest}
      /\ LET i == m.dest IN
         IF state[i] = StateLeader THEN
           LET entry == [term |-> currentTerm[i], cmd |-> m.cmd, client |-> m.source] IN
           /\ logVar' = [logVar EXCEPT ![i] = Append(logVar[i], entry)]
           /\ Network' = Network \ {m}
           /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>
         ELSE
           LET reply ==
             [ type |-> IF m.type = ClientPutRequest THEN ClientPutResponse ELSE ClientGetResponse,
               term |-> 0,
               source |-> i, dest |-> m.source,
               lastLogTerm |-> 0, lastLogIndex |-> 0,
               voteGranted |-> FALSE,
               prevLogIndex |-> 0, prevLogTerm |-> 0,
               entries |-> << >>,
               commitIndex |-> 0,
               success |-> FALSE,
               matchIndex |-> 0,
               cmd |-> Nil,
               response |-> [idx |-> m.cmd.idx, key |-> m.cmd.key, value |-> Nil, ok |-> FALSE],
               leaderHint |-> leaderVar[i] ] IN
           /\ Network' = (Network \ {m}) \cup {reply}
           /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>

ClientSend(c) ==
    /\ c \in Clients
    /\ ClientReqIdx[c] < MaxClientReq
    /\ LET k == ClientReqIdx[c] + 1 IN
       LET destSrv == IF ClLeader[c] # Nil THEN ClLeader[c] ELSE CHOOSE s \in Servers: TRUE IN
       LET isPut == CHOOSE b \in BOOLEAN: TRUE IN
       LET cmd ==
         IF isPut THEN
           [type |-> Put, key |-> CHOOSE x \in Keys: TRUE, value |-> CHOOSE v \in Values: TRUE, idx |-> k]
         ELSE
           [type |-> Get, key |-> CHOOSE x \in Keys: TRUE, value |-> Nil, idx |-> k] IN
       LET m ==
         [ type |-> IF isPut THEN ClientPutRequest ELSE ClientGetRequest,
           term |-> 0,
           source |-> c, dest |-> destSrv,
           lastLogTerm |-> 0, lastLogIndex |-> 0,
           voteGranted |-> FALSE,
           prevLogIndex |-> 0, prevLogTerm |-> 0,
           entries |-> << >>,
           commitIndex |-> 0,
           success |-> FALSE,
           matchIndex |-> 0,
           cmd |-> cmd,
           response |-> Nil,
           leaderHint |-> Nil ] IN
       /\ ClientReqIdx' = [ClientReqIdx EXCEPT ![c] = k]
       /\ Network' = Network \cup {m}
       /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader >>

ClientReceive ==
    \E m \in Network:
      /\ m.dest \in Clients
      /\ LET c == m.dest IN
         /\ ClLeader' = [ClLeader EXCEPT ![c] = m.leaderHint]
         /\ Network' = Network \ {m}
         /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClientReqIdx >>

SendHeartbeat(i, j) == SendAE(i, j)

Drop ==
    \E m \in Network:
      /\ Network' = Network \ {m}
      /\ UNCHANGED << state, currentTerm, votedFor, leaderVar, logVar, commitIndex, lastApplied, nextIndex, matchIndex, votesResponded, votesGranted, Timeout, KV, KVDomain, ClLeader, ClientReqIdx >>

Next ==
    \/ \E i \in Servers: LeaderTimeout(i)
    \/ \E i \in Servers: Tick(i)
    \/ \E i, j \in Servers: i # j /\ SendRVQ(i, j)
    \/ DeliverRVQ
    \/ DeliverRVP
    \/ \E i, j \in Servers: i # j /\ SendAE(i, j)
    \/ DeliverAEQ
    \/ DeliverAEP
    \/ \E i \in Servers: AdvanceCommit(i)
    \/ \E i \in Servers: ApplyCommitted(i)
    \/ DeliverClientReq
    \/ \E c \in Clients: ClientSend(c)
    \/ ClientReceive
    \/ Drop

Spec ==
    Init
    /\ [][Next]_vars
    /\ \A i \in Servers: WF_vars(LeaderTimeout(i))
    /\ WF_vars(DeliverRVQ \/ DeliverRVP \/ DeliverAEQ \/ DeliverAEP \/ DeliverClientReq \/ ClientReceive)
    /\ \A p \in Servers: \A q \in Servers \ {p}: WF_vars(SendAE(p, q))
    /\ \A r \in Servers: WF_vars(ApplyCommitted(r))

====