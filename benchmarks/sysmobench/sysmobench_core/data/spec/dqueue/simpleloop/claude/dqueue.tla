---- MODULE dqueue ----

EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS NUM_CONSUMERS, PRODUCER

VARIABLES net, proc, s, pc, requester

vars == <<net, proc, s, pc, requester>>

NUM_NODES == NUM_CONSUMERS + 1

Consumers == 1..NUM_CONSUMERS
Nodes == Consumers \cup {PRODUCER}

TypeOK == 
    /\ net \in [Nodes -> Seq(Nodes \cup Nat)]
    /\ proc \in [Consumers -> (Nodes \cup Nat)]
    /\ s \in Nat
    /\ pc \in [Nodes -> {"c", "c1", "c2", "p", "p1", "p2", "Done"}]
    /\ requester \in Nodes

Init ==
    /\ net = [n \in Nodes |-> <<>>]
    /\ proc = [c \in Consumers |-> c]
    /\ s = 0
    /\ pc = [n \in Nodes |-> IF n = PRODUCER THEN "p" ELSE "c"]
    /\ requester = PRODUCER

ConsumerC(self) ==
    /\ pc[self] = "c"
    /\ pc' = [pc EXCEPT ![self] = "c1"]
    /\ UNCHANGED <<net, proc, s, requester>>

ConsumerC1(self) ==
    /\ pc[self] = "c1"
    /\ net' = [net EXCEPT ![PRODUCER] = Append(@, self)]
    /\ pc' = [pc EXCEPT ![self] = "c2"]
    /\ UNCHANGED <<proc, s, requester>>

ConsumerC2(self) ==
    /\ pc[self] = "c2"
    /\ Len(net[self]) > 0
    /\ proc' = [proc EXCEPT ![self] = Head(net[self])]
    /\ net' = [net EXCEPT ![self] = Tail(@)]
    /\ pc' = [pc EXCEPT ![self] = "c"]
    /\ UNCHANGED <<s, requester>>

ProducerP ==
    /\ pc[PRODUCER] = "p"
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p1"]
    /\ UNCHANGED <<net, proc, s, requester>>

ProducerP1 ==
    /\ pc[PRODUCER] = "p1"
    /\ Len(net[PRODUCER]) > 0
    /\ requester' = Head(net[PRODUCER])
    /\ net' = [net EXCEPT ![PRODUCER] = Tail(@)]
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p2"]
    /\ UNCHANGED <<proc, s>>

ProducerP2 ==
    /\ pc[PRODUCER] = "p2"
    /\ net' = [net EXCEPT ![requester] = Append(@, s)]
    /\ s' = s + 1
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p"]
    /\ UNCHANGED <<proc, requester>>

Next ==
    \/ ProducerP
    \/ ProducerP1
    \/ ProducerP2
    \/ \E self \in Consumers:
        \/ ConsumerC(self)
        \/ ConsumerC1(self)
        \/ ConsumerC2(self)

Spec == Init /\ [][Next]_vars

====