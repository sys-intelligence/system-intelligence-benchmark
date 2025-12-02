(* Generic module that aims to handle trace specifications *)
(* Modified to support Subsequence Matching with Bounded Internal Steps *)
---- MODULE TraceSpec ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, Bags, Json, IOUtils, TVOperators

ASSUME TLCGet("config").mode = "bfs"

CONSTANT MaxInternalSteps

VARIABLES l, internal_steps

(* Operators to override *)
Vars == Print(<<"Trace spec isn't valid, you should override 'Vars'.">>, <<>>)
BaseInit == Print(<<"Trace spec isn't valid, you should override 'BaseInit'.">>, Nil)
BaseNext == Print(<<"Trace spec isn't valid, you should override 'BaseNext'.">>, Nil)
TraceNext == Print(<<"Trace spec isn't valid, you should override 'TraceNext'.">>, Nil)
UpdateVariables(logline) == Print(<<"Trace spec isn't valid, you should override 'UpdateVariables'.">>, Nil)

(* Read trace *)
Trace ==
    IF "TRACE_PATH" \in DOMAIN IOEnv THEN
        ndJsonDeserialize(IOEnv.TRACE_PATH)
    ELSE
        Print(<<"TRACE_PATH environnement variable not found, use default trace file.">>, ndJsonDeserialize("trace.ndjson"))

(* Read config *)
Config ==
    IF "CONFIG_PATH" \in DOMAIN IOEnv THEN
        ndJsonDeserialize(IOEnv.CONFIG_PATH)
    ELSE
        Print(<<"CONFIG_PATH environnement variable not found, use default config file.">>, ndJsonDeserialize("conf.ndjson"))

(* Manage exceptions *)
ASSUME \A t \in ToSet(Trace) : "event" \notin DOMAIN t \/ ("event" \in DOMAIN t /\ t.event /= "__exception")

logline ==
    Trace[l]
    
IsEvent(e) ==
    /\ l \in 1..Len(Trace)
    /\ IF "event" \in DOMAIN logline THEN logline.event = e ELSE TRUE
    /\ l' = l + 1
    /\ internal_steps' = 0
    /\ UpdateVariables(logline)
    /\ l' >= TLCGet(0) => TLCSet(0, l')

TraceInit ==
    /\ l = 1
    /\ internal_steps = 0
    /\ BaseInit
    /\ TLCSet(0, 0)

InternalStep ==
    /\ l \in 1..Len(Trace)
    /\ internal_steps < MaxInternalSteps
    /\ l' = l
    /\ internal_steps' = internal_steps + 1
    /\ BaseNext

TraceSpec ==
    TraceInit /\ [][TraceNext \/ InternalStep]_<<l, internal_steps, Vars>>

TraceAccepted ==
    LET d == TLCGet(0) IN
    IF d - 1 = Len(Trace) THEN TRUE
    ELSE Print(<<"Failed matching the trace to (a prefix of) a behavior:", Trace[d],
                    "TLA+ debugger breakpoint hit count " \o ToString(d+1)>>, FALSE)

TraceView ==
    <<Vars, internal_steps, TLCGet("level")>>

Termination ==
    l = Len(Trace) + 1  => TLCSet("exit", TRUE)

====
