---- MODULE dqueueValidate ----
EXTENDS IOUtils, TLCExt, Naturals, FiniteSetsExt, Sequences, TLC, Integers

__all_strings == TLCCache(IODeserialize("dqueueAllStrings.bin", FALSE), {"allStrings"})

CONSTANT defaultInitValue, BUFFER_SIZE, NUM_CONSUMERS, PRODUCER

\* Additional defns start
AConsumer_net_read(__state0, self, __idx0, __value, __rest(_)) ==
  /\ (Len(((__state0)["network"])[__idx0])) > (0)
  /\ LET msg == Head(((__state0)["network"])[__idx0])
         __state1 == [__state0 EXCEPT !.network[__idx0] = Tail(((__state0)["network"])[__idx0])]
     IN  /\ msg = __value
         /\ __rest(__state1)

AConsumer_net_write(__state0, self, __idx0, __value, __rest(_)) ==
  /\ (Len(((__state0)["network"])[__idx0])) < (BUFFER_SIZE)
  /\ LET __state1 == [__state0 EXCEPT !.network[__idx0] = Append(((__state0)["network"])[__idx0], __value)]
     IN  /\ __rest(__state1)
AProducer_net_read(__state0, self, __idx0, __value, __rest(_)) ==
  /\ (Len(((__state0)["network"])[__idx0])) > (0)
  /\ LET msg == Head(((__state0)["network"])[__idx0])
         __state1 == [__state0 EXCEPT !.network[__idx0] = Tail(((__state0)["network"])[__idx0])]
     IN  /\ msg = __value
         /\ __rest(__state1)

AProducer_net_write(__state0, self, __idx0, __value, __rest(_)) ==
  /\ (Len(((__state0)["network"])[__idx0])) < (BUFFER_SIZE)
  /\ LET __state1 == [__state0 EXCEPT !.network[__idx0] = Append(((__state0)["network"])[__idx0], __value)]
     IN  /\ __rest(__state1)
AProducer_s_read(__state0, self, __value, __rest(_)) ==
  LET __state1 == [__state0 EXCEPT !.stream = (((__state0)["stream"]) + (1)) % (BUFFER_SIZE)]
  IN  /\ (__state1)["stream"] = __value
      /\ __rest(__state1)

AProducer_s_write(__state0, self, __value, __rest(_)) ==
  LET __state1 == [__state0 EXCEPT !.stream = (__state0)["stream"]]
  IN  /\ __rest(__state1)
\* Additional defns end

VARIABLES __action, __clock, network, pc, processor, requester, stream

vars == <<__action, __clock, network, pc, processor, requester, stream>>
__user_vars == <<network, pc, processor, requester, stream>>

__clock_at(__clk, __idx) ==
  IF __idx \in DOMAIN __clk
  THEN __clk[__idx]
  ELSE 0

__time_lt_pair(__pair1, __pair2) ==
  \/ __pair1[1] < __pair2[1]
  \/ /\ __pair1[1] = __pair2[1]
      /\ __pair1[2] < __pair2[2]

__time_lt_rec(__rec1, __rec2) ==
  __time_lt_pair(__rec1.endTime, __rec2.startTime)

__records == TLCCache(IODeserialize("dqueueValidateData.bin", FALSE), {"validateData"})

__clock_check(self, __commit(_)) ==
  LET __idx == __clock_at(__clock, self) + 1
      __updated_clock == (self :> __idx) @@ __clock \* this way round!
      __next_clock == __records[self][__idx].clock
  IN  /\ __idx \in DOMAIN __records[self]
      /\ __updated_clock[self] = __next_clock[self]
      /\ \A __i \in DOMAIN __next_clock :
           __next_clock[__i] <= __clock_at(__updated_clock, __i)
      /\ __commit(__updated_clock)

__state_get == [
  network |-> network, 
  pc |-> pc, 
  processor |-> processor, 
  requester |-> requester, 
  stream |-> stream]

__state_set(__state_prime) ==
  /\ network' = __state_prime.network
  /\ pc' = __state_prime.pc
  /\ processor' = __state_prime.processor
  /\ requester' = __state_prime.requester
  /\ stream' = __state_prime.stream

__instance == INSTANCE dqueue


AProducer_p_0(self, __commit(_, _)) ==
  (__clock_at(__clock, self) + 1) \in DOMAIN __records[self] /\
  LET __state0 == __state_get
      __record == __records[self][__clock_at(__clock, self) + 1]
      __elems == __record.elems
  IN  /\ pc[self] = "p"
      /\ __record.pc = "p"
      /\ Len(__elems) = 1
      /\ \lnot __record.isAbort
      /\ __elems[1].name = ".pc"
      /\ LET __state1 == [__state0 EXCEPT !.pc[self] = "p1"]
         IN  /\ __commit(__state1, __record)

AProducer_p1_0(self, __commit(_, _)) ==
  (__clock_at(__clock, self) + 1) \in DOMAIN __records[self] /\
  LET __state0 == __state_get
      __record == __records[self][__clock_at(__clock, self) + 1]
      __elems == __record.elems
  IN  /\ pc[self] = "p1"
      /\ __record.pc = "p1"
      /\ Len(__elems) = 3
      /\ \lnot __record.isAbort
      /\ __elems[1].name = "AProducer.net"
      /\ AProducer_net_read(__state0, self, __elems[1].indices[1], __elems[1].value, LAMBDA __state1:
           /\ __elems[2].name = "AProducer.requester"
           /\ LET __state2 == [__state1 EXCEPT !.requester[self] = __elems[2].value]
              IN  /\ __elems[3].name = ".pc"
                  /\ LET __state3 == [__state2 EXCEPT !.pc[self] = "p2"]
                     IN  /\ __commit(__state3, __record))

AConsumer_c_0(self, __commit(_, _)) ==
  (__clock_at(__clock, self) + 1) \in DOMAIN __records[self] /\
  LET __state0 == __state_get
      __record == __records[self][__clock_at(__clock, self) + 1]
      __elems == __record.elems
  IN  /\ pc[self] = "c"
      /\ __record.pc = "c"
      /\ Len(__elems) = 1
      /\ \lnot __record.isAbort
      /\ __elems[1].name = ".pc"
      /\ LET __state1 == [__state0 EXCEPT !.pc[self] = "c1"]
         IN  /\ __commit(__state1, __record)

AConsumer_c1_0(self, __commit(_, _)) ==
  (__clock_at(__clock, self) + 1) \in DOMAIN __records[self] /\
  LET __state0 == __state_get
      __record == __records[self][__clock_at(__clock, self) + 1]
      __elems == __record.elems
  IN  /\ pc[self] = "c1"
      /\ __record.pc = "c1"
      /\ Len(__elems) = 2
      /\ \lnot __record.isAbort
      /\ __elems[1].name = "AConsumer.net"
      /\ AConsumer_net_write(__state0, self, __elems[1].indices[1], __elems[1].value, LAMBDA __state1:
           /\ __elems[2].name = ".pc"
           /\ LET __state2 == [__state1 EXCEPT !.pc[self] = "c2"]
              IN  /\ __commit(__state2, __record))
__self_values == {0, 1}

__Init ==
  /\ __instance!Init
  /\ __clock = <<>>
  /\ __action = <<>>

__Next_self(self, __commit(_, _)) ==
  \/ AConsumer_c_0(self, __commit)
  \/ AConsumer_c1_0(self, __commit)
  \/ AProducer_p_0(self, __commit)
  \/ AProducer_p1_0(self, __commit)

__Next ==
  \E self \in __self_values :
    /\ __clock_check(self, LAMBDA __clk : __clock' = __clk)
    /\ __Next_self(self, LAMBDA __state, __record :
        /\ __action' = __record
        /\ __state_set(__state))

__dbg_alias == [
  __action |-> __action,
  __clock |-> __clock,
  network |-> network,
  pc |-> pc,
  processor |-> processor,
  requester |-> requester,
  stream |-> stream,
  __dbg_alias |-> [self \in __self_values |->
    IF   __clock_at(__clock, self) + 1 \in DOMAIN __records[self]
    THEN LET __rec == __records[self][__clock_at(__clock, self) + 1]
         IN  __rec @@ [
           depends_on |-> { __i \in __self_values :
             /\ __i # self
             /\ __clock_at(__rec.clock, __i) > __clock_at(__clock, __i)
           }
         ]
    ELSE <<>>
  ]
]

__LoopAtEnd ==
  /\ \A self \in __self_values :
    __clock_at(__clock, self) = Len(__records[self])
  /\ UNCHANGED vars

__TerminateAtEnd ==
  [][__LoopAtEnd => TLCSet("exit", TRUE)]_vars

__Spec ==
  /\ __Init
  /\ [][__Next \/ __LoopAtEnd]_vars

__Stuttering ==
  /\ __clock' # __clock
  /\ UNCHANGED __user_vars

__IsRefinement == [][__instance!Next \/ __Stuttering]_vars

__progress_inv_0 ==
  __clock_check(0, LAMBDA _a : TRUE) => __Next_self(0, LAMBDA _a, _b : TRUE)

__progress_inv_1 ==
  __clock_check(1, LAMBDA _a : TRUE) => __Next_self(1, LAMBDA _a, _b : TRUE)

====
