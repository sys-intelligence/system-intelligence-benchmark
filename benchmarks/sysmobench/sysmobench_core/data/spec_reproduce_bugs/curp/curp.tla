---- MODULE curp ----
EXTENDS TLC, Sequences, SequencesExt, Naturals, FiniteSets, FiniteSetsExt, Bags, Integers

\* Reproduce Bug: https://github.com/xline-kv/Xline/pull/582

CONSTANTS
    Replicas,
    Commands,
    Nil,
    Keys,
    CmdTerm,        \* 每个命令对应的“term”（抽象 fast_round 中的 term）
    LocalLeaderCmd, \* 客户端认为的旧 leader 返回的命令
    NoCmd           \* fast_round 尚未返回结果时的哨兵值

ASSUME IsFiniteSet(Replicas)
ASSUME IsFiniteSet(Commands)
ASSUME Nil \notin Replicas
ASSUME \A cmd \in Commands: cmd \in [key: Keys]

\* term 信息：每个命令都有一个 term，用来区分“新 leader 的结果”和“旧 leader 的结果”
ASSUME CmdTerm \in [Commands -> Nat]

\* 本地视角下 leader 返回的命令，term 较小（旧 leader）
ASSUME LocalLeaderCmd \in Commands

ReplicasScenario == {0, 1, 2, 3, 4}
KeysScenario == {"k1", "k2", "NoCmdKey"}
CmdFor(k) == [key |-> k]
CommandsScenario == {CmdFor("k1"), CmdFor("k2")}
CmdTermScenario ==
    [cmd \in CommandsScenario |->
        IF cmd = CmdFor("k1")
            THEN 1
            ELSE 2]
LocalLeaderCmdScenario == CmdFor("k1")
NilScenario == -1
NoCmdScenario == CmdFor("NoCmdKey")

(***************************************************************************)
(* Variables                                                               *)
(***************************************************************************)

VARIABLES
    term,
    leader,
    role,
    speculativePool,
    uncommittedPool,
    log,
    commitIndex,
    lastApplied,
    pendingProposals,
    clientResult   \* fast_round 聚合后的结果（客户端最终“看到”的命令）

vars ==
    << term, leader, role, speculativePool, uncommittedPool,
       log, commitIndex, lastApplied, pendingProposals, clientResult >>

(***************************************************************************)
(* Basic operators                                                         *)
(***************************************************************************)

Max2(a, b) == IF a >= b THEN a ELSE b

TypeOK ==
    /\ term \in Nat
    /\ leader \in Replicas \cup {Nil}
    /\ role \in [Replicas -> {"Leader", "Follower"}]
    /\ speculativePool \in [Replicas -> SUBSET Commands]
    /\ uncommittedPool \in [Replicas -> SUBSET Commands]
    /\ log \in [Replicas -> Seq(Commands)]
    /\ commitIndex \in [Replicas -> Nat]
    /\ lastApplied \in [Replicas -> Nat]
    /\ pendingProposals \in [Replicas -> SUBSET Commands]
    /\ clientResult \in Commands \cup {NoCmd}

Init ==
    /\ term = 0
    /\ leader = Nil
    /\ role = [r \in Replicas |-> "Follower"]
    /\ speculativePool = [r \in Replicas |-> {}]
    /\ uncommittedPool = [r \in Replicas |-> {}]
    /\ log = [r \in Replicas |-> <<>>]
    /\ commitIndex = [r \in Replicas |-> 0]
    /\ lastApplied = [r \in Replicas |-> 0]
    /\ pendingProposals = [r \in Replicas |-> {}]
    /\ clientResult = NoCmd

\* Quorum definitions based on the number of replicas
QuorumSize == (Cardinality(Replicas) \div 2) + 1
RecoverQuorumSize == (QuorumSize \div 2) + 1

\* Operator to check for command conflicts based on keys
Conflicts(c1, c2) == c1["key"] = c2["key"]

(***************************************************************************)
(* 1. Client proposes a command to all replicas                             *)
(***************************************************************************)

Propose(cmd) ==
    /\ cmd \in Commands
    /\ pendingProposals' =
        [r \in Replicas |-> pendingProposals[r] \cup {cmd}]
    /\ UNCHANGED
        << term, leader, role, speculativePool, uncommittedPool,
           log, commitIndex, lastApplied, clientResult >>

(***************************************************************************)
(* 2. Leader processes a proposed command                                  *)
(***************************************************************************)

ProcessProposeLeader(r, cmd) ==
    /\ r \in Replicas
    /\ role[r] = "Leader"
    /\ cmd \in pendingProposals[r]
    /\ LET conflict ==
            \E c_prime \in (speculativePool[r] \cup uncommittedPool[r]) :
                Conflicts(cmd, c_prime)
       IN
        /\ pendingProposals' =
            [pendingProposals EXCEPT ![r] =
                pendingProposals[r] \ {cmd}]
        /\ speculativePool' =
            [speculativePool EXCEPT ![r] =
                speculativePool[r] \cup {cmd}]
        /\ IF ~conflict THEN
              /\ uncommittedPool' =
                    [uncommittedPool EXCEPT ![r] =
                        uncommittedPool[r] \cup {cmd}]
              /\ log' =
                    [log EXCEPT ![r] = Append(log[r], cmd)]
           ELSE
              /\ UNCHANGED << uncommittedPool, log >>
    /\ UNCHANGED
        << term, leader, role, commitIndex, lastApplied, clientResult >>

(***************************************************************************)
(* 3. Non-leader processes a proposed command                              *)
(***************************************************************************)

ProcessProposeNonLeader(r, cmd) ==
    /\ r \in Replicas
    /\ role[r] = "Follower"
    /\ cmd \in pendingProposals[r]
    /\ pendingProposals' =
        [pendingProposals EXCEPT ![r] =
            pendingProposals[r] \ {cmd}]
    /\ speculativePool' =
        [speculativePool EXCEPT ![r] =
            speculativePool[r] \cup {cmd}]
    /\ UNCHANGED
        << term, leader, role, uncommittedPool, log,
           commitIndex, lastApplied, clientResult >>

(***************************************************************************)
(* 4. Backend consensus protocol commits a command                         *)
(***************************************************************************)

Commit ==
    /\ leader /= Nil
    /\ \E i \in 1..Len(log[leader]) :
        /\ i > commitIndex[leader]
        /\ LET cmd == log[leader][i]
           IN
            /\ Cardinality(
                  {r \in Replicas :
                      Len(log[r]) >= i /\ log[r][i] = cmd}
               ) >= QuorumSize
            /\ commitIndex' =
                [r \in Replicas |-> 
                    IF Len(log[r]) >= i /\ log[r][i] = cmd
                    THEN Max2(commitIndex[r], i)
                    ELSE commitIndex[r]]
            /\ UNCHANGED
                << term, leader, role, pendingProposals,
                   speculativePool, uncommittedPool, log,
                   lastApplied, clientResult >>

(***************************************************************************)
(* 5. Replica processes a committed command and applies garbage collection *)
(***************************************************************************)

ProcessCommitMsg(r, i) ==
    /\ r \in Replicas
    /\ i \in 1..Len(log[r])
    /\ i > lastApplied[r]
    /\ i <= commitIndex[r]
    /\ LET cmd == log[r][i]
       IN
        /\ lastApplied' =
            [lastApplied EXCEPT ![r] = i]
        /\ speculativePool' =
            [speculativePool EXCEPT ![r] =
                speculativePool[r] \ {cmd}]
        /\ uncommittedPool' =
            [uncommittedPool EXCEPT ![r] =
                uncommittedPool[r] \ {cmd}]
        /\ UNCHANGED
            << term, leader, role, pendingProposals,
               log, commitIndex, clientResult >>

(***************************************************************************)
(* 6. Backend protocol elects a new leader and recovers state              *)
(***************************************************************************)

LeaderChange(l) ==
    /\ l \in Replicas
    /\ leader /= l
    /\ \E Q_vote \in SUBSET Replicas:
        /\ Cardinality(Q_vote) >= QuorumSize
        /\ LET
            AllSpecCmdsBag ==
                BagUnion({SetToBag(speculativePool[r]) : r \in Q_vote})
            RecoveredCmds ==
                { cmd \in DOMAIN AllSpecCmdsBag :
                      AllSpecCmdsBag[cmd] >= RecoverQuorumSize }
           IN
            /\ term' = term + 1
            /\ leader' = l
            /\ role' =
                [r \in Replicas |->
                    IF r = l THEN "Leader" ELSE "Follower"]
            /\ uncommittedPool' =
                [uncommittedPool EXCEPT ![l] = RecoveredCmds]
            /\ speculativePool' =
                [speculativePool EXCEPT ![l] = RecoveredCmds]
            /\ log' =
                [log EXCEPT ![l] =
                    log[l] \o SetToSeq(RecoveredCmds)]
            /\ UNCHANGED
                << pendingProposals, commitIndex,
                   lastApplied, clientResult >>

(***************************************************************************)
(* 7. fast_round 行为（含 bug）：在高 term 结果和本地 leader 结果之间选择     *)
(***************************************************************************)

\* 所有命令中最大的 term
HighestCmdTerm ==
    Max({ CmdTerm[cmd] : cmd \in Commands })

\* 所有“最高 term”的命令（抽象新 leader 的结果集合）
HighestTermCmds ==
    { cmd \in Commands : CmdTerm[cmd] = HighestCmdTerm }

\* 语义上“正确”的结果（应该从最高 term 的结果中选）
CorrectCmd ==
    CHOOSE cmd \in HighestTermCmds : TRUE

\* Bug：fast_round 把“最高 term 的结果”和 LocalLeaderCmd 一起作为候选，
\*      非确定性地选择其一 → 在存在旧 leader 的时候可能返回旧结果。
FastRoundBug ==
    /\ clientResult = NoCmd
    /\ (HighestTermCmds \cup {LocalLeaderCmd}) # {}
    /\ clientResult' \in (HighestTermCmds \cup {LocalLeaderCmd})
    /\ UNCHANGED
        << term, leader, role, speculativePool, uncommittedPool,
           log, commitIndex, lastApplied, pendingProposals >>

(***************************************************************************)
(* Next                                                                   *)
(***************************************************************************)

Next ==
    \/ \E cmd \in Commands : Propose(cmd)
    \/ \E r \in Replicas :
          \E cmd \in pendingProposals[r] :
              ProcessProposeLeader(r, cmd)
    \/ \E r \in Replicas :
          \E cmd \in pendingProposals[r] :
              ProcessProposeNonLeader(r, cmd)
    \/ Commit
    \/ \E r \in Replicas :
          \E i \in 1..Len(log[r]) :
              ProcessCommitMsg(r, i)
    \/ \E l \in Replicas : LeaderChange(l)
    \/ FastRoundBug

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

(***************************************************************************)
(* Safety property: fast_round 必须返回最高 term 对应的命令                *)
(***************************************************************************)

FastRoundSafe ==
    clientResult \in Commands => clientResult = CorrectCmd

NoLowerTermResult ==
    ~(clientResult \in Commands /\ CmdTerm[clientResult] < HighestCmdTerm)

==== 
