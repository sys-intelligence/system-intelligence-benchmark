------------------------------- MODULE 1_mutex -------------------------------

EXTENDS Integers, Sequences, TLC

\* Reproduce Bug: https://github.com/asterinas/asterinas/pull/1279

CONSTANTS NumProcs, NONE

Procs == 1..NumProcs

ThreadPhases ==
    {"Start", "TryLock", "BugClear", "WaitEnqueue", "CheckLock",
     "AwaitWake", "CS", "UnlockRelease", "WakeStart", "WakeLoop",
     "WakeUp", "Done"}

VARIABLES locked, waitQueueNum, waitQueue, hasWoken, guardHeld, wakeTarget, phase

vars == << locked, waitQueueNum, waitQueue, hasWoken, guardHeld, wakeTarget, phase >>

Init ==
    /\ locked = FALSE
    /\ waitQueue = << >>
    /\ waitQueueNum = 0
    /\ hasWoken = [t \in Procs |-> FALSE]
    /\ guardHeld = [t \in Procs |-> FALSE]
    /\ wakeTarget = [t \in Procs |-> NONE]
    /\ phase = [t \in Procs |-> "Start"]

StartAdvance(t) ==
    /\ phase[t] = "Start"
    /\ phase' = [phase EXCEPT ![t] = "TryLock"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, hasWoken, guardHeld, wakeTarget >>

TryLockAcquire(t) ==
    /\ phase[t] = "TryLock"
    /\ locked = FALSE
    /\ locked' = TRUE
    /\ guardHeld' = [guardHeld EXCEPT ![t] = TRUE]
    /\ phase' = [phase EXCEPT ![t] = "CS"]
    /\ UNCHANGED << waitQueue, waitQueueNum, hasWoken, wakeTarget >>

TryLockBusy(t) ==
    /\ phase[t] = "TryLock"
    /\ locked = TRUE
    /\ phase' = [phase EXCEPT ![t] = "BugClear"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, hasWoken, guardHeld, wakeTarget >>

BugClear(t) ==
    /\ phase[t] = "BugClear"
    /\ locked' = FALSE
    /\ phase' = [phase EXCEPT ![t] = "WaitEnqueue"]
    /\ UNCHANGED << waitQueue, waitQueueNum, hasWoken, guardHeld, wakeTarget >>

WaitEnqueue(t) ==
    /\ phase[t] = "WaitEnqueue"
    /\ waitQueue' = Append(waitQueue, t)
    /\ waitQueueNum' = waitQueueNum + 1
    /\ phase' = [phase EXCEPT ![t] = "CheckLock"]
    /\ UNCHANGED << locked, hasWoken, guardHeld, wakeTarget >>

CheckLockAcquire(t) ==
    /\ phase[t] = "CheckLock"
    /\ locked = FALSE
    /\ locked' = TRUE
    /\ guardHeld' = [guardHeld EXCEPT ![t] = TRUE]
    /\ hasWoken' = [hasWoken EXCEPT ![t] = TRUE]
    /\ phase' = [phase EXCEPT ![t] = "CS"]
    /\ UNCHANGED << waitQueue, waitQueueNum, wakeTarget >>

CheckLockWait(t) ==
    /\ phase[t] = "CheckLock"
    /\ locked = TRUE
    /\ phase' = [phase EXCEPT ![t] = "AwaitWake"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, hasWoken, guardHeld, wakeTarget >>

AwaitWake(t) ==
    /\ phase[t] = "AwaitWake"
    /\ hasWoken[t] = TRUE
    /\ hasWoken' = [hasWoken EXCEPT ![t] = FALSE]
    /\ phase' = [phase EXCEPT ![t] = "WaitEnqueue"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, guardHeld, wakeTarget >>

CSProgress(t) ==
    /\ phase[t] = "CS"
    /\ phase' = [phase EXCEPT ![t] = "UnlockRelease"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, hasWoken, guardHeld, wakeTarget >>

UnlockRelease(t) ==
    /\ phase[t] = "UnlockRelease"
    /\ locked' = FALSE
    /\ guardHeld' = [guardHeld EXCEPT ![t] = FALSE]
    /\ phase' = [phase EXCEPT ![t] = "WakeStart"]
    /\ UNCHANGED << waitQueue, waitQueueNum, hasWoken, wakeTarget >>

WakeStartIdle(t) ==
    /\ phase[t] = "WakeStart"
    /\ waitQueueNum = 0
    /\ phase' = [phase EXCEPT ![t] = "Done"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, hasWoken, guardHeld, wakeTarget >>

WakeStartActive(t) ==
    /\ phase[t] = "WakeStart"
    /\ waitQueueNum # 0
    /\ phase' = [phase EXCEPT ![t] = "WakeLoop"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, hasWoken, guardHeld, wakeTarget >>

WakeLoopDequeue(t) ==
    /\ phase[t] = "WakeLoop"
    /\ waitQueueNum # 0
    /\ LET head == Head(waitQueue) IN
         /\ waitQueue' = Tail(waitQueue)
         /\ waitQueueNum' = waitQueueNum - 1
         /\ wakeTarget' = [wakeTarget EXCEPT ![t] = head]
    /\ phase' = [phase EXCEPT ![t] = "WakeUp"]
    /\ UNCHANGED << locked, hasWoken, guardHeld >>

WakeLoopEmpty(t) ==
    /\ phase[t] = "WakeLoop"
    /\ waitQueueNum = 0
    /\ phase' = [phase EXCEPT ![t] = "Done"]
    /\ wakeTarget' = [wakeTarget EXCEPT ![t] = NONE]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, hasWoken, guardHeld >>

WakeUpDeliver(t) ==
    /\ phase[t] = "WakeUp"
    /\ wakeTarget[t] # NONE
    /\ hasWoken[wakeTarget[t]] = FALSE
    /\ hasWoken' = [hasWoken EXCEPT ![wakeTarget[t]] = TRUE]
    /\ wakeTarget' = [wakeTarget EXCEPT ![t] = NONE]
    /\ phase' = [phase EXCEPT ![t] = "Done"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, guardHeld >>

WakeUpSkip(t) ==
    /\ phase[t] = "WakeUp"
    /\ wakeTarget[t] # NONE
    /\ hasWoken[wakeTarget[t]] = TRUE
    /\ wakeTarget' = [wakeTarget EXCEPT ![t] = NONE]
    /\ phase' = [phase EXCEPT ![t] = "WakeLoop"]
    /\ UNCHANGED << locked, waitQueue, waitQueueNum, hasWoken, guardHeld >>

ThreadNext(t) ==
      StartAdvance(t)
    \/ TryLockAcquire(t)
    \/ TryLockBusy(t)
    \/ BugClear(t)
    \/ WaitEnqueue(t)
    \/ CheckLockAcquire(t)
    \/ CheckLockWait(t)
    \/ AwaitWake(t)
    \/ CSProgress(t)
    \/ UnlockRelease(t)
    \/ WakeStartIdle(t)
    \/ WakeStartActive(t)
    \/ WakeLoopDequeue(t)
    \/ WakeLoopEmpty(t)
    \/ WakeUpDeliver(t)
    \/ WakeUpSkip(t)

Terminating ==
    /\ \A t \in Procs : phase[t] = "Done"
    /\ UNCHANGED vars

Next == (\E t \in Procs : ThreadNext(t)) \/ Terminating

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A t \in Procs : WF_vars(ThreadNext(t))

MutualExclusion ==
    \A i, j \in Procs :
        (i # j) => ~ (phase[i] = "CS" /\ phase[j] = "CS")

Trying(i) ==
    phase[i] \in {"TryLock", "BugClear", "WaitEnqueue", "CheckLock", "AwaitWake"}

DeadAndLivelockFree ==
    \E i \in Procs :
        Trying(i) ~> (\E j \in Procs : phase[j] = "CS")

StarvationFree ==
    \A i \in Procs :
        Trying(i) ~> (phase[i] = "CS")

Termination ==
    <>(\A t \in Procs : phase[t] = "Done")

=============================================================================
