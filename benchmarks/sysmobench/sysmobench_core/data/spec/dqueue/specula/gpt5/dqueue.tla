---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS Val, Consumers, PRODUCER, Null

Node == {PRODUCER} \cup Consumers

ReqMsg(c) == [type |-> "request", c |-> c, v |-> Null]
ProdMsg(v) == [type |-> "produce", c |-> Null, v |-> v]

\* Renamed to avoid conflict with Sequences' Head/Tail
Head_(s) == s[1]
Tail_(s) == IF Len(s) = 0 THEN <<>> ELSE SubSeq(s, 2, Len(s))

VARIABLES state, net, reqBuf, s, proc

vars == << state, net, reqBuf, s, proc >>

Init ==
    /\ PRODUCER \notin Consumers
    /\ state = [n \in Node |-> IF n = PRODUCER THEN "p" ELSE "c"]
    /\ net = [n \in Node |-> <<>>]
    /\ reqBuf = Null
    /\ s \in UNION { [1..i -> Val] : i \in 0..Cardinality(Val) }
    /\ proc = [c \in Consumers |-> Null]

CEnter(c) ==
    /\ c \in Consumers
    /\ state[c] = "c"
    /\ state' = [state EXCEPT ![c] = "c1"]
    /\ UNCHANGED << net, reqBuf, s, proc >>

Request(c) ==
    /\ c \in Consumers
    /\ state[c] = "c1"
    /\ net' = [net EXCEPT ![PRODUCER] = net[PRODUCER] \o << ReqMsg(c) >>]
    /\ state' = [state EXCEPT ![c] = "c2"]
    /\ UNCHANGED << reqBuf, s, proc >>

Consume(c) ==
    /\ c \in Consumers
    /\ state[c] = "c2"
    /\ Len(net[c]) >= 1
    /\ Head_(net[c]).type = "produce"
    /\ LET m == Head_(net[c]) IN
       /\ net' = [net EXCEPT ![c] = Tail_(net[c])]
       /\ proc' = [proc EXCEPT ![c] = m.v]
       /\ state' = [state EXCEPT ![c] = "c"]
       /\ UNCHANGED << reqBuf, s >>

PEnter ==
    /\ state[PRODUCER] = "p"
    /\ state' = [state EXCEPT ![PRODUCER] = "p1"]
    /\ UNCHANGED << net, reqBuf, s, proc >>

ProdRecvReq ==
    /\ state[PRODUCER] = "p1"
    /\ Len(net[PRODUCER]) >= 1
    /\ Head_(net[PRODUCER]).type = "request"
    /\ LET m == Head_(net[PRODUCER]) IN
       /\ net' = [net EXCEPT ![PRODUCER] = Tail_(net[PRODUCER])]
       /\ reqBuf' = m.c
       /\ state' = [state EXCEPT ![PRODUCER] = "p2"]
       /\ UNCHANGED << s, proc >>

Produce ==
    /\ state[PRODUCER] = "p2"
    /\ reqBuf \in Consumers
    /\ Len(s) >= 1
    /\ net' = [net EXCEPT ![reqBuf] = net[reqBuf] \o << ProdMsg(Head_(s)) >>]
    /\ s' = Tail_(s)
    /\ state' = [state EXCEPT ![PRODUCER] = "p"]
    /\ reqBuf' = Null
    /\ UNCHANGED proc

Next ==
    \/ \E c \in Consumers : CEnter(c)
    \/ \E c \in Consumers : Request(c)
    \/ \E c \in Consumers : Consume(c)
    \/ PEnter
    \/ ProdRecvReq
    \/ Produce

Spec == Init /\ [][Next]_vars

====