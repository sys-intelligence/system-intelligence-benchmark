---- MODULE TestSpec ----
EXTENDS Integers

\* This should cause Send to be added as both variable and function
TestAction == 
    /\ Send(message)  \* Function usage
    /\ UNCHANGED Send  \* Variable usage (this line makes Send look like a variable)

====
