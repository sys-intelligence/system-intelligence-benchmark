---- MODULE 1_etcdraft ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

\* Reproduce Bug: https://github.com/etcd-io/etcd/pull/10998

CONSTANTS
    Servers,
    InitialVoters,
    InitialLearners

VARIABLES
    currentTerm,
    state,
    votedFor,
    log,
    commitIndex,
    configuration,
    messages

vars == <<currentTerm, state, votedFor, log, commitIndex, configuration, messages>>

----

Follower == "Follower"
Candidate == "Candidate"
Leader == "Leader"

Nil == "Nil"

----

Message ==
    [mtype: {"RequestVote"},
     mterm: Nat,
     msource: Servers,
     mdest: Servers,
     mlastLogTerm: Nat,
     mlastLogIndex: Nat]
    \cup
    [mtype: {"RequestVoteResponse"},
     mterm: Nat,
     msource: Servers,
     mdest: Servers,
     mvoteGranted: BOOLEAN]
    \cup
    [mtype: {"AppendEntries"},
     mterm: Nat,
     msource: Servers,
     mdest: Servers,
     mprevLogIndex: Nat,
     mprevLogTerm: Nat,
     mentries: Seq([term: Nat, type: {"Normal", "Config"}, config: [voters: SUBSET Servers, learners: SUBSET Servers]]),
     mcommitIndex: Nat]
    \cup
    [mtype: {"AppendEntriesResponse"},
     mterm: Nat,
     msource: Servers,
     mdest: Servers,
     msuccess: BOOLEAN,
     mmatchIndex: Nat]

----

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

GetConfig(s) == configuration[s]

IsVoter(s) == s \in GetConfig(s).voters

IsLearner(s) == s \in GetConfig(s).learners

QuorumSize(config) == (Cardinality(config.voters) \div 2) + 1

----

Init ==
    /\ currentTerm = [s \in Servers |-> 0]
    /\ state = [s \in Servers |-> Follower]
    /\ votedFor = [s \in Servers |-> Nil]
    /\ log = [s \in Servers |-> <<>>]
    /\ commitIndex = [s \in Servers |-> 0]
    /\ configuration = [s \in Servers |->
        [voters |-> InitialVoters, learners |-> InitialLearners]]
    /\ messages = {}

----

Send(m) == messages' = messages \cup {m}

Discard(m) == messages' = messages \ {m}

Reply(response, request) ==
    messages' = (messages \ {request}) \cup {response}

----

Restart(s) ==
    /\ state' = [state EXCEPT ![s] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<currentTerm, log, commitIndex, configuration, messages>>

Timeout(s) ==
    /\ state[s] \in {Follower, Candidate}
    /\ state' = [state EXCEPT ![s] = Candidate]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = currentTerm[s] + 1]
    /\ votedFor' = [votedFor EXCEPT ![s] = s]
    /\ messages' = messages \cup {
        [mtype |-> "RequestVote",
         mterm |-> currentTerm[s] + 1,
         msource |-> s,
         mdest |-> d,
         mlastLogTerm |-> LastTerm(log[s]),
         mlastLogIndex |-> Len(log[s])]
        : d \in Servers \ {s}}
    /\ UNCHANGED <<log, commitIndex, configuration>>

----

HandleRequestVoteRequest(s, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[s])
                 \/ /\ m.mlastLogTerm = LastTerm(log[s])
                    /\ m.mlastLogIndex >= Len(log[s])
        grant == /\ logOk
                 /\ votedFor[s] \in {Nil, m.msource}
                 /\ IsVoter(s)
    IN
        /\ IF grant
           THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.msource]
                /\ Reply([mtype |-> "RequestVoteResponse",
                         mterm |-> currentTerm[s],
                         msource |-> s,
                         mdest |-> m.msource,
                         mvoteGranted |-> TRUE], m)
           ELSE /\ Reply([mtype |-> "RequestVoteResponse",
                         mterm |-> currentTerm[s],
                         msource |-> s,
                         mdest |-> m.msource,
                         mvoteGranted |-> FALSE], m)
                /\ UNCHANGED votedFor
        /\ UNCHANGED <<currentTerm, state, log, commitIndex, configuration>>

HandleRequestVoteResponse(s, m) ==
    /\ m.mterm = currentTerm[s]
    /\ state[s] = Candidate
    /\ LET voteQuorum == {s} \cup {v \in Servers :
            /\ \E msg \in messages :
                /\ msg.mtype = "RequestVoteResponse"
                /\ msg.mdest = s
                /\ msg.msource = v
                /\ msg.mterm = currentTerm[s]
                /\ msg.mvoteGranted}
       IN
        IF Cardinality(voteQuorum) >= QuorumSize(GetConfig(s))
        THEN /\ state' = [state EXCEPT ![s] = Leader]
             /\ messages' = messages \cup {
                 [mtype |-> "AppendEntries",
                  mterm |-> currentTerm[s],
                  msource |-> s,
                  mdest |-> d,
                  mprevLogIndex |-> Len(log[s]),
                  mprevLogTerm |-> LastTerm(log[s]),
                  mentries |-> <<>>,
                  mcommitIndex |-> commitIndex[s]]
                 : d \in Servers \ {s}}
             /\ UNCHANGED <<currentTerm, votedFor, log, commitIndex, configuration>>
        ELSE /\ UNCHANGED vars

----

AppendEntries(s) ==
    /\ state[s] = Leader
    /\ LET d == CHOOSE dest \in Servers \ {s} : TRUE
       IN Send([mtype |-> "AppendEntries",
                mterm |-> currentTerm[s],
                msource |-> s,
                mdest |-> d,
                mprevLogIndex |-> Len(log[s]),
                mprevLogTerm |-> LastTerm(log[s]),
                mentries |-> <<>>,
                mcommitIndex |-> commitIndex[s]])
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, configuration>>

HandleAppendEntriesRequest(s, m) ==
    LET logOk == \/ m.mprevLogIndex = 0
                 \/ /\ m.mprevLogIndex > 0
                    /\ m.mprevLogIndex <= Len(log[s])
                    /\ m.mprevLogTerm = log[s][m.mprevLogIndex].term
    IN
        /\ m.mterm = currentTerm[s]
        /\ IF logOk
           THEN /\ log' = [log EXCEPT ![s] =
                    SubSeq(log[s], 1, m.mprevLogIndex) \o m.mentries]
                /\ commitIndex' = [commitIndex EXCEPT ![s] = m.mcommitIndex]
                /\ LET newConfig == IF Len(m.mentries) > 0 /\ m.mentries[Len(m.mentries)].type = "Config"
                                    THEN m.mentries[Len(m.mentries)].config
                                    ELSE configuration[s]
                   IN configuration' = [configuration EXCEPT ![s] = newConfig]
                /\ Reply([mtype |-> "AppendEntriesResponse",
                         mterm |-> currentTerm[s],
                         msource |-> s,
                         mdest |-> m.msource,
                         msuccess |-> TRUE,
                         mmatchIndex |-> m.mprevLogIndex + Len(m.mentries)], m)
                /\ UNCHANGED <<currentTerm, state, votedFor>>
           ELSE /\ Reply([mtype |-> "AppendEntriesResponse",
                         mterm |-> currentTerm[s],
                         msource |-> s,
                         mdest |-> m.msource,
                         msuccess |-> FALSE,
                         mmatchIndex |-> 0], m)
                /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, configuration>>

----

PromoteLearner(s, learner) ==
    /\ state[s] = Leader
    /\ learner \in GetConfig(s).learners
    /\ LET newConfig == [voters |-> GetConfig(s).voters \cup {learner},
                         learners |-> GetConfig(s).learners \ {learner}]
           configEntry == [term |-> currentTerm[s],
                          type |-> "Config",
                          config |-> newConfig]
       IN /\ log' = [log EXCEPT ![s] = Append(log[s], configEntry)]
          /\ configuration' = [configuration EXCEPT ![s] = newConfig]
          /\ UNCHANGED <<currentTerm, state, votedFor, commitIndex, messages>>

AdvanceCommitIndex(s) ==
    /\ state[s] = Leader
    /\ LET Agree(index) ==
            Cardinality({s} \cup {t \in Servers :
                /\ t \in GetConfig(s).voters
                /\ Len(log[t]) >= index
                /\ log[t][index].term = currentTerm[s]}) >= QuorumSize(GetConfig(s))
           newCommitIndex == CHOOSE index \in (commitIndex[s]+1)..Len(log[s]) :
                               /\ Agree(index)
                               /\ \A i \in (commitIndex[s]+1)..(index-1) : ~Agree(i)
       IN /\ commitIndex[s] < Len(log[s])
          /\ Agree(commitIndex[s] + 1)
          /\ commitIndex' = [commitIndex EXCEPT ![s] = newCommitIndex]
          /\ UNCHANGED <<currentTerm, state, votedFor, log, configuration, messages>>

----

UpdateTerm(s, m) ==
    /\ m.mterm > currentTerm[s]
    /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
    /\ state' = [state EXCEPT ![s] = Follower]
    /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
    /\ UNCHANGED <<log, commitIndex, configuration>>

HandleRequestVoteRequestWithTermUpdate(s, m) ==
    LET logOk == \/ m.mlastLogTerm > LastTerm(log[s])
                 \/ /\ m.mlastLogTerm = LastTerm(log[s])
                    /\ m.mlastLogIndex >= Len(log[s])
        grant == /\ logOk
                 /\ IsVoter(s)
    IN
        /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
        /\ state' = [state EXCEPT ![s] = Follower]
        /\ IF grant
           THEN /\ votedFor' = [votedFor EXCEPT ![s] = m.msource]
                /\ Reply([mtype |-> "RequestVoteResponse",
                         mterm |-> m.mterm,
                         msource |-> s,
                         mdest |-> m.msource,
                         mvoteGranted |-> TRUE], m)
           ELSE /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
                /\ Reply([mtype |-> "RequestVoteResponse",
                         mterm |-> m.mterm,
                         msource |-> s,
                         mdest |-> m.msource,
                         mvoteGranted |-> FALSE], m)
        /\ UNCHANGED <<log, commitIndex, configuration>>

ReceiveMessage(s, m) ==
    /\ m \in messages
    /\ m.mdest = s
    /\ IF m.mterm > currentTerm[s]
       THEN CASE m.mtype = "RequestVote" ->
                  HandleRequestVoteRequestWithTermUpdate(s, m)
              [] m.mtype = "AppendEntries" ->
                  /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                  /\ state' = [state EXCEPT ![s] = Follower]
                  /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
                  /\ HandleAppendEntriesRequest(s, m)
              [] OTHER ->
                  /\ currentTerm' = [currentTerm EXCEPT ![s] = m.mterm]
                  /\ state' = [state EXCEPT ![s] = Follower]
                  /\ votedFor' = [votedFor EXCEPT ![s] = Nil]
                  /\ Discard(m)
                  /\ UNCHANGED <<log, commitIndex, configuration>>
       ELSE CASE m.mtype = "RequestVote" ->
                  HandleRequestVoteRequest(s, m)
              [] m.mtype = "RequestVoteResponse" ->
                  HandleRequestVoteResponse(s, m)
              [] m.mtype = "AppendEntries" ->
                  HandleAppendEntriesRequest(s, m)
              [] OTHER ->
                  /\ Discard(m)
                  /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, configuration>>

DropMessage(m) ==
    /\ Discard(m)
    /\ UNCHANGED <<currentTerm, state, votedFor, log, commitIndex, configuration>>

----

Next ==
    \/ \E s \in Servers : Restart(s)
    \/ \E s \in Servers : Timeout(s)
    \/ \E s \in Servers : AppendEntries(s)
    \/ \E s \in Servers, l \in Servers : PromoteLearner(s, l)
    \/ \E s \in Servers : AdvanceCommitIndex(s)
    \/ \E s \in Servers, m \in messages : ReceiveMessage(s, m)
    \/ \E m \in messages : DropMessage(m)

Spec == Init /\ [][Next]_vars

----

ElectionSafety ==
    \A s1, s2 \in Servers :
        (state[s1] = Leader /\ state[s2] = Leader /\ currentTerm[s1] = currentTerm[s2])
        => (s1 = s2)

LogMatching ==
    \A s1, s2 \in Servers :
        \A i \in 1..Len(log[s1]) :
            (i <= Len(log[s2]) /\ log[s1][i].term = log[s2][i].term)
            => (log[s1][i] = log[s2][i])

LeaderAppendOnly ==
    [][\A s \in Servers :
        state[s] = Leader =>
            \A i \in 1..Len(log[s]) : (log'[s])[i] = (log[s])[i]]_vars

EventuallyElectLeader ==
    <>(\E s \in Servers : state[s] = Leader)

StateConstraint ==
    \A s \in Servers : currentTerm[s] <= 3

====
