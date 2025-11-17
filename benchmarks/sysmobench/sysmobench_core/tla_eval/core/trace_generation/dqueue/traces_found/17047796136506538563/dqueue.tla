---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NUM_CONSUMERS, PRODUCER, DATA

VARIABLES 
    pc,
    net,
    requester,
    proc

vars == <<pc, net, requester, proc>>

Consumers == 1..NUM_CONSUMERS
Processes == Consumers \cup {PRODUCER}

Init == 
    /\ pc = [p \in Processes |-> IF p = PRODUCER THEN "p" ELSE "c"]
    /\ net = [p \in Processes |-> <<>>]
    /\ requester = 0
    /\ proc = [c \in Consumers |-> 0]

ConsumerStart(c) ==
    /\ pc[c] = "c"
    /\ pc' = [pc EXCEPT ![c] = "c1"]
    /\ UNCHANGED <<net, requester, proc>>

ConsumerRequest(c) ==
    /\ pc[c] = "c1"
    /\ net' = [net EXCEPT ![PRODUCER] = Append(@, c)]
    /\ pc' = [pc EXCEPT ![c] = "c2"]
    /\ UNCHANGED <<requester, proc>>

ConsumerReceive(c) ==
    /\ pc[c] = "c2"
    /\ Len(net[c]) > 0
    /\ proc' = [proc EXCEPT ![c] = Head(net[c])]
    /\ net' = [net EXCEPT ![c] = Tail(@)]
    /\ pc' = [pc EXCEPT ![c] = "c"]
    /\ UNCHANGED requester

ProducerStart ==
    /\ pc[PRODUCER] = "p"
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p1"]
    /\ UNCHANGED <<net, requester, proc>>

ProducerReceiveRequest ==
    /\ pc[PRODUCER] = "p1"
    /\ Len(net[PRODUCER]) > 0
    /\ requester' = Head(net[PRODUCER])
    /\ net' = [net EXCEPT ![PRODUCER] = Tail(@)]
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p2"]
    /\ UNCHANGED proc

ProducerSendResponse ==
    /\ pc[PRODUCER] = "p2"
    /\ requester \in Consumers
    /\ net' = [net EXCEPT ![requester] = Append(@, DATA)]
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p"]
    /\ UNCHANGED <<requester, proc>>

Next == 
    \/ \E c \in Consumers : ConsumerStart(c)
    \/ \E c \in Consumers : ConsumerRequest(c)
    \/ \E c \in Consumers : ConsumerReceive(c)
    \/ ProducerStart
    \/ ProducerReceiveRequest
    \/ ProducerSendResponse

Spec == Init /\ [][Next]_vars

====