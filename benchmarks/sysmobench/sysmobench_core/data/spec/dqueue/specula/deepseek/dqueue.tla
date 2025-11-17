---- MODULE dqueue ----
EXTENDS Naturals, Sequences, FiniteSets, TLC, Bags
CONSTANTS Consumers, Producer
VARIABLES consumerState, producerState, network, pendingRequests
Nodes == Consumers ∪ {Producer}
Message == {"request", "produce"}
vars == <<consumerState, producerState, network, pendingRequests>>
Init == 
    consumerState = [c \in Consumers |-> "c"]
    /\ producerState = "p"
    /\ network = [pair \in Nodes × Nodes |-> << >>]
    /\ pendingRequests = {}
ConsumerSend(c) == 
    /\ consumerState[c] = "c"
    /\ network' = [network EXCEPT ![c, Producer] = Append(@, "request")]
    /\ consumerState' = [consumerState EXCEPT ![c] = "c2"]
    /\ UNCHANGED <<producerState, pendingRequests>>
ConsumerReceive(c) == 
    /\ consumerState[c] = "c2"
    /\ network[Producer, c] # << >>
    /\ Head(network[Producer, c]) = "produce"
    /\ network' = [network EXCEPT ![Producer, c] = Tail(@)]
    /\ consumerState' = [consumerState EXCEPT ![c] = "c"]
    /\ UNCHANGED <<producerState, pendingRequests>>
ProducerReceive(c) == 
    /\ producerState = "p"
    /\ network[c, Producer] # << >>
    /\ Head(network[c, Producer]) = "request"
    /\ network' = [network EXCEPT ![c, Producer] = Tail(@)]
    /\ pendingRequests' = pendingRequests ∪ {c}
    /\ producerState' = "p2"
    /\ UNCHANGED <<consumerState>>
ProducerSend(c) == 
    /\ producerState = "p2"
    /\ c \in pendingRequests
    /\ network' = [network EXCEPT ![Producer, c] = Append(@, "produce")]
    /\ pendingRequests' = pendingRequests \ {c}
    /\ producerState' = "p"
    /\ UNCHANGED <<consumerState>>
Next == 
    \/ \E c \in Consumers : ConsumerSend(c)
    \/ \E c \in Consumers : ConsumerReceive(c)
    \/ \E c \in Consumers : ProducerReceive(c)
    \/ \E c \in pendingRequests : ProducerSend(c)
Spec == Init /\ [][Next]_vars
====