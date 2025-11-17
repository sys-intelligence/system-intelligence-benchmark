---- MODULE raftkvs ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Integers

CONSTANTS NumServers, NumClients, MaxNodeFail, ExploreFail, Debug, LeaderTimeoutReset, LogPop, LogConcat, AllStrings

VARIABLES 
    net,
    netLen,
    netEnabled,
    fd,
    state,
    currentTerm,
    log,
    plog,
    commitIndex,
    nextIndex,
    matchIndex,
    votedFor,
    votesResponded,
    votesGranted,
    leader,
    sm,
    smDomain,
    leaderTimeout,
    appendEntriesCh,
    becomeLeaderCh,
    reqCh,
    respCh,
    timeout

vars == <<net, netLen, netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

Nil == 0
Put == "put"
Get == "get"
Follower == "follower"
Candidate == "candidate"
Leader == "leader"
RequestVoteRequest == "rvq"
RequestVoteResponse == "rvp"
AppendEntriesRequest == "apq"
AppendEntriesResponse == "app"
ClientPutRequest == "cpq"
ClientPutResponse == "cpp"
ClientGetRequest == "cgq"
ClientGetResponse == "cgp"

ServerSet == 1..NumServers
ClientSet == (6*NumServers + 1)..(6*NumServers + NumClients)
NodeSet == ServerSet \cup ClientSet

IsQuorum(s) == Cardinality(s) * 2 > NumServers

LastTerm(xlog) == IF Len(xlog) = 0 THEN 0 ELSE xlog[Len(xlog)].term

Min(S) == CHOOSE x \in S : \A y \in S : x <= y

Max(S) == CHOOSE x \in S : \A y \in S : x >= y

Init == 
    /\ net = [i \in NodeSet |-> <<>>]
    /\ netLen = [i \in NodeSet |-> 0]
    /\ netEnabled = [i \in ServerSet |-> TRUE]
    /\ fd = [i \in ServerSet |-> FALSE]
    /\ state = [i \in ServerSet |-> Follower]
    /\ currentTerm = [i \in ServerSet |-> 0]
    /\ log = [i \in ServerSet |-> <<>>]
    /\ plog = [i \in ServerSet |-> [cmd |-> LogPop, cnt |-> 0]]
    /\ commitIndex = [i \in ServerSet |-> 0]
    /\ nextIndex = [i \in ServerSet |-> [j \in ServerSet |-> 1]]
    /\ matchIndex = [i \in ServerSet |-> [j \in ServerSet |-> 0]]
    /\ votedFor = [i \in ServerSet |-> Nil]
    /\ votesResponded = [i \in ServerSet |-> {}]
    /\ votesGranted = [i \in ServerSet |-> {}]
    /\ leader = [i \in ServerSet |-> Nil]
    /\ sm = [i \in ServerSet |-> [k \in {} |-> Nil]]
    /\ smDomain = [i \in ServerSet |-> {}]
    /\ leaderTimeout = FALSE
    /\ appendEntriesCh = [i \in ServerSet |-> FALSE]
    /\ becomeLeaderCh = [i \in ServerSet |-> FALSE]
    /\ reqCh = <<>>
    /\ respCh = <<>>
    /\ timeout = FALSE

LeaderTimeout ==
    /\ leaderTimeout = FALSE
    /\ \E i \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ state[i] \in {Follower, Candidate}
        /\ netLen[i] = 0
        /\ state' = [state EXCEPT ![i] = Candidate]
        /\ currentTerm' = [currentTerm EXCEPT ![i] = currentTerm[i] + 1]
        /\ votedFor' = [votedFor EXCEPT ![i] = i]
        /\ votesResponded' = [votesResponded EXCEPT ![i] = {i}]
        /\ votesGranted' = [votesGranted EXCEPT ![i] = {i}]
        /\ leader' = [leader EXCEPT ![i] = Nil]
        /\ leaderTimeout' = LeaderTimeoutReset
        /\ UNCHANGED <<net, netLen, netEnabled, fd, log, plog, commitIndex, nextIndex, matchIndex, sm, smDomain, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

HandleRequestVoteRequest ==
    \E i, j \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ Len(net[i]) > 0
        /\ LET m == Head(net[i]) IN
            /\ m.mtype = RequestVoteRequest
            /\ m.mdest = i
            /\ m.msource = j
            /\ IF m.mterm > currentTerm[i] THEN
                /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                /\ state' = [state EXCEPT ![i] = Follower]
                /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                /\ leader' = [leader EXCEPT ![i] = Nil]
               ELSE
                /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
            /\ LET logOK == \/ m.mlastLogTerm > LastTerm(log[i])
                            \/ /\ m.mlastLogTerm = LastTerm(log[i])
                               /\ m.mlastLogIndex >= Len(log[i])
                   grant == /\ m.mterm = currentTerm'[i]
                            /\ logOK
                            /\ votedFor'[i] \in {Nil, j}
               IN
                /\ IF grant THEN votedFor' = [votedFor' EXCEPT ![i] = j] ELSE UNCHANGED votedFor
                /\ net' = [net EXCEPT ![j] = Append(net[j], [mtype |-> RequestVoteResponse, mterm |-> currentTerm'[i], mvoteGranted |-> grant, msource |-> i, mdest |-> j])]
                /\ net' = [net' EXCEPT ![i] = Tail(net[i])]
                /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1, ![j] = netLen[j] + 1]
        /\ UNCHANGED <<netEnabled, fd, log, plog, commitIndex, nextIndex, matchIndex, votesResponded, votesGranted, sm, smDomain, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

HandleRequestVoteResponse ==
    \E i, j \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ Len(net[i]) > 0
        /\ LET m == Head(net[i]) IN
            /\ m.mtype = RequestVoteResponse
            /\ m.mdest = i
            /\ m.msource = j
            /\ IF m.mterm > currentTerm[i] THEN
                /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                /\ state' = [state EXCEPT ![i] = Follower]
                /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                /\ leader' = [leader EXCEPT ![i] = Nil]
                /\ net' = [net EXCEPT ![i] = Tail(net[i])]
                /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
               ELSE IF m.mterm < currentTerm[i] THEN
                /\ net' = [net EXCEPT ![i] = Tail(net[i])]
                /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
                /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
               ELSE
                /\ m.mterm = currentTerm[i]
                /\ votesResponded' = [votesResponded EXCEPT ![i] = votesResponded[i] \cup {j}]
                /\ IF m.mvoteGranted THEN
                    /\ leaderTimeout' = LeaderTimeoutReset
                    /\ votesGranted' = [votesGranted EXCEPT ![i] = votesGranted[i] \cup {j}]
                    /\ IF state[i] = Candidate /\ IsQuorum(votesGranted'[i]) THEN
                        becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = TRUE]
                       ELSE
                        UNCHANGED becomeLeaderCh
                   ELSE
                    /\ UNCHANGED <<leaderTimeout, votesGranted, becomeLeaderCh>>
                /\ net' = [net EXCEPT ![i] = Tail(net[i])]
                /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
                /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
        /\ UNCHANGED <<netEnabled, fd, log, plog, commitIndex, nextIndex, matchIndex, sm, smDomain, appendEntriesCh, reqCh, respCh, timeout>>

HandleAppendEntriesRequest ==
    \E i, j \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ Len(net[i]) > 0
        /\ LET m == Head(net[i]) IN
            /\ m.mtype = AppendEntriesRequest
            /\ m.mdest = i
            /\ m.msource = j
            /\ IF m.mterm > currentTerm[i] THEN
                /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                /\ state' = [state EXCEPT ![i] = Follower]
                /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                /\ leader' = [leader EXCEPT ![i] = Nil]
               ELSE
                /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
            /\ LET logOK == \/ m.mprevLogIndex = 0
                            \/ /\ m.mprevLogIndex > 0
                               /\ m.mprevLogIndex <= Len(log[i])
                               /\ m.mprevLogTerm = log[i][m.mprevLogIndex].term
               IN
                /\ IF m.mterm = currentTerm'[i] THEN
                    /\ leader' = [leader' EXCEPT ![i] = m.msource]
                    /\ leaderTimeout' = LeaderTimeoutReset
                   ELSE
                    /\ UNCHANGED leaderTimeout
                /\ IF m.mterm = currentTerm'[i] /\ state'[i] = Candidate THEN
                    state' = [state' EXCEPT ![i] = Follower]
                   ELSE
                    UNCHANGED state
                /\ IF \/ m.mterm < currentTerm'[i]
                      \/ /\ m.mterm = currentTerm'[i]
                         /\ state'[i] = Follower
                         /\ ~logOK
                   THEN
                    /\ net' = [net EXCEPT ![j] = Append(net[j], [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[i], msuccess |-> FALSE, mmatchIndex |-> 0, msource |-> i, mdest |-> j])]
                    /\ net' = [net' EXCEPT ![i] = Tail(net[i])]
                    /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1, ![j] = netLen[j] + 1]
                    /\ UNCHANGED <<log, plog, commitIndex, sm, smDomain>>
                   ELSE
                    /\ m.mterm = currentTerm'[i] /\ state'[i] = Follower /\ logOK
                    /\ log' = [log EXCEPT ![i] = SubSeq(log[i], 1, m.mprevLogIndex) \o m.mentries]
                    /\ plog' = [plog EXCEPT ![i] = [cmd |-> LogConcat, entries |-> m.mentries]]
                    /\ LET newCommitIndex == Min({m.mcommitIndex, Len(log'[i])})
                       IN
                        /\ commitIndex' = [commitIndex EXCEPT ![i] = Max({commitIndex[i], newCommitIndex})]
                        /\ sm' = sm
                        /\ smDomain' = smDomain
                    /\ net' = [net EXCEPT ![j] = Append(net[j], [mtype |-> AppendEntriesResponse, mterm |-> currentTerm'[i], msuccess |-> TRUE, mmatchIndex |-> m.mprevLogIndex + Len(m.mentries), msource |-> i, mdest |-> j])]
                    /\ net' = [net' EXCEPT ![i] = Tail(net[i])]
                    /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1, ![j] = netLen[j] + 1]
        /\ UNCHANGED <<netEnabled, fd, nextIndex, matchIndex, votesResponded, votesGranted, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

HandleAppendEntriesResponse ==
    \E i, j \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ Len(net[i]) > 0
        /\ LET m == Head(net[i]) IN
            /\ m.mtype = AppendEntriesResponse
            /\ m.mdest = i
            /\ m.msource = j
            /\ IF m.mterm > currentTerm[i] THEN
                /\ currentTerm' = [currentTerm EXCEPT ![i] = m.mterm]
                /\ state' = [state EXCEPT ![i] = Follower]
                /\ votedFor' = [votedFor EXCEPT ![i] = Nil]
                /\ leader' = [leader EXCEPT ![i] = Nil]
               ELSE IF m.mterm < currentTerm[i] THEN
                /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
               ELSE
                /\ leaderTimeout' = LeaderTimeoutReset
                /\ m.mterm = currentTerm[i]
                /\ IF m.msuccess THEN
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = m.mmatchIndex + 1]
                    /\ matchIndex' = [matchIndex EXCEPT ![i][j] = m.mmatchIndex]
                   ELSE
                    /\ nextIndex' = [nextIndex EXCEPT ![i][j] = Max({nextIndex[i][j] - 1, 1})]
                    /\ UNCHANGED matchIndex
                /\ UNCHANGED <<currentTerm, state, votedFor, leader>>
            /\ net' = [net EXCEPT ![i] = Tail(net[i])]
            /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
        /\ UNCHANGED <<netEnabled, fd, log, plog, commitIndex, votesResponded, votesGranted, sm, smDomain, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

HandleClientRequest ==
    \E i \in ServerSet, c \in ClientSet :
        /\ netEnabled[i] = TRUE
        /\ Len(net[i]) > 0
        /\ LET m == Head(net[i]) IN
            /\ m.mtype \in {ClientPutRequest, ClientGetRequest}
            /\ m.mdest = i
            /\ m.msource = c
            /\ IF state[i] = Leader THEN
                /\ LET entry == [term |-> currentTerm[i], cmd |-> m.mcmd, client |-> m.msource]
                   IN
                    /\ log' = [log EXCEPT ![i] = Append(log[i], entry)]
                    /\ plog' = [plog EXCEPT ![i] = [cmd |-> LogConcat, entries |-> <<entry>>]]
                    /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
               ELSE
                /\ LET respType == IF m.mcmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
                   IN
                    net' = [net EXCEPT ![c] = Append(net[c], [mtype |-> respType, msuccess |-> FALSE, mresponse |-> [idx |-> m.mcmd.idx, key |-> m.mcmd.key], mleaderHint |-> leader[i], msource |-> i, mdest |-> c])]
                /\ UNCHANGED <<log, plog, appendEntriesCh>>
            /\ net' = [net' EXCEPT ![i] = Tail(net[i])]
            /\ netLen' = [netLen EXCEPT ![i] = netLen[i] - 1]
        /\ UNCHANGED <<netEnabled, fd, state, currentTerm, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, becomeLeaderCh, reqCh, respCh, timeout>>

BecomeLeader ==
    \E i \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ becomeLeaderCh[i] = TRUE
        /\ state[i] = Candidate
        /\ IsQuorum(votesGranted[i])
        /\ state' = [state EXCEPT ![i] = Leader]
        /\ nextIndex' = [nextIndex EXCEPT ![i] = [j \in ServerSet |-> Len(log[i]) + 1]]
        /\ matchIndex' = [matchIndex EXCEPT ![i] = [j \in ServerSet |-> 0]]
        /\ leader' = [leader EXCEPT ![i] = i]
        /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = TRUE]
        /\ becomeLeaderCh' = [becomeLeaderCh EXCEPT ![i] = FALSE]
        /\ UNCHANGED <<net, netLen, netEnabled, fd, currentTerm, log, plog, commitIndex, votedFor, votesResponded, votesGranted, sm, smDomain, leaderTimeout, reqCh, respCh, timeout>>

AdvanceCommitIndex ==
    \E i \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ state[i] = Leader
        /\ \E newCommitIndex \in (commitIndex[i] + 1)..Len(log[i]) :
            /\ log[i][newCommitIndex].term = currentTerm[i]
            /\ IsQuorum({i} \cup {j \in ServerSet : matchIndex[i][j] >= newCommitIndex})
            /\ commitIndex' = [commitIndex EXCEPT ![i] = newCommitIndex]
            /\ LET entry == log[i][newCommitIndex]
                   cmd == entry.cmd
                   respType == IF cmd.type = Put THEN ClientPutResponse ELSE ClientGetResponse
               IN
                /\ IF cmd.type = Put THEN
                    /\ sm' = [sm EXCEPT ![i] = sm[i] @@ (cmd.key :> cmd.value)]
                    /\ smDomain' = [smDomain EXCEPT ![i] = smDomain[i] \cup {cmd.key}]
                   ELSE
                    /\ UNCHANGED <<sm, smDomain>>
                /\ LET reqOK == cmd.key \in smDomain'[i]
                   IN
                    net' = [net EXCEPT ![entry.client] = Append(net[entry.client], [mtype |-> respType, msuccess |-> TRUE, mresponse |-> [idx |-> cmd.idx, key |-> cmd.key, value |-> IF reqOK THEN sm'[i][cmd.key] ELSE Nil, ok |-> reqOK], mleaderHint |-> i, msource |-> i, mdest |-> entry.client])]
        /\ UNCHANGED <<netLen, netEnabled, fd, state, currentTerm, log, plog, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, leaderTimeout, appendEntriesCh, becomeLeaderCh, reqCh, respCh, timeout>>

SendAppendEntries ==
    \E i, j \in ServerSet :
        /\ netEnabled[i] = TRUE
        /\ state[i] = Leader
        /\ appendEntriesCh[i] = TRUE
        /\ i # j
        /\ LET prevLogIndex == nextIndex[i][j] - 1
               prevLogTerm == IF prevLogIndex > 0 THEN log[i][prevLogIndex].term ELSE 0
               entries == SubSeq(log[i], nextIndex[i][j], Len(log[i]))
           IN
            /\ net' = [net EXCEPT ![j] = Append(net[j], [mtype |-> AppendEntriesRequest, mterm |-> currentTerm[i], mprevLogIndex |-> prevLogIndex, mprevLogTerm |-> prevLogTerm, mentries |-> entries, mcommitIndex |-> commitIndex[i], msource |-> i, mdest |-> j])]
            /\ netLen' = [netLen EXCEPT ![j] = netLen[j] + 1]
        /\ appendEntriesCh' = [appendEntriesCh EXCEPT ![i] = FALSE]
        /\ UNCHANGED <<netEnabled, fd, state, currentTerm, log, plog, commitIndex, nextIndex, matchIndex, votedFor, votesResponded, votesGranted, leader, sm, smDomain, leaderTimeout, becomeLeaderCh, reqCh, respCh, timeout>>

Next == 
    \/ LeaderTimeout
    \/ HandleRequestVoteRequest
    \/ HandleRequestVoteResponse
    \/ HandleAppendEntriesRequest
    \/ HandleAppendEntriesResponse
    \/ HandleClientRequest
    \/ BecomeLeader
    \/ AdvanceCommitIndex
    \/ SendAppendEntries

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

====