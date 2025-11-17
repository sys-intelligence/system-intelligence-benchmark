---- MODULE dqueue ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags

CONSTANTS
    PRODUCER,
    CONSUMERS,
    Data

ASSUME PRODUCER \notin CONSUMERS
ASSUME IsFiniteSet(CONSUMERS) /\ CONSUMERS /= {}
ASSUME IsFiniteSet(Data) /\ Data /= {}

VARIABLES
    pc,
    net,
    requester

vars == <<pc, net, requester>>

Process == CONSUMERS \cup {PRODUCER}
ConsumerStates == {"c", "c1", "c2"}
ProducerStates == {"p", "p1", "p2"}

Init ==
    /\ pc = [i \in Process |-> IF i = PRODUCER THEN "p" ELSE "c"]
    /\ net = [i \in Process |-> <<>>]
    /\ requester \in CONSUMERS

ConsumerPrepareRequest(i) ==
    /\ i \in CONSUMERS
    /\ pc[i] = "c"
    /\ pc' = [pc EXCEPT ![i] = "c1"]
    /\ UNCHANGED <<net, requester>>

ConsumerSendRequest(i) ==
    /\ i \in CONSUMERS
    /\ pc[i] = "c1"
    /\ LET msg == [type |-> "request", from |-> i]
       IN net' = [net EXCEPT ![PRODUCER] = Append(@, msg)]
    /\ pc' = [pc EXCEPT ![i] = "c2"]
    /\ UNCHANGED <<requester>>

ConsumerReceiveProduce(i) ==
    /\ i \in CONSUMERS
    /\ pc[i] = "c2"
    /\ Len(net[i]) > 0
    /\ Head(net[i]).type = "produce"
    /\ net' = [net EXCEPT ![i] = Tail(@)]
    /\ pc' = [pc EXCEPT ![i] = "c"]
    /\ UNCHANGED <<requester>>

ProducerPrepare ==
    /\ pc[PRODUCER] = "p"
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p1"]
    /\ UNCHANGED <<net, requester>>

ProducerReceiveRequest ==
    /\ pc[PRODUCER] = "p1"
    /\ Len(net[PRODUCER]) > 0
    /\ LET msg == Head(net[PRODUCER])
       IN /\ msg.type = "request"
          /\ requester' = msg.from
    /\ net' = [net EXCEPT ![PRODUCER] = Tail(@)]
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p2"]

ProducerSendProduce ==
    /\ pc[PRODUCER] = "p2"
    /\ \E d \in Data:
        LET msg == [type |-> "produce", data |-> d]
        IN net' = [net EXCEPT ![requester] = Append(@, msg)]
    /\ pc' = [pc EXCEPT ![PRODUCER] = "p"]
    /\ UNCHANGED <<requester>>

Next ==
    \/ \E i \in CONSUMERS : ConsumerPrepareRequest(i)
    \/ \E i \in CONSUMERS : ConsumerSendRequest(i)
    \/ \E i \in CONSUMERS : ConsumerReceiveProduce(i)
    \/ ProducerPrepare
    \/ ProducerReceiveRequest
    \/ ProducerSendProduce

Spec == Init /\ [][Next]_vars

====