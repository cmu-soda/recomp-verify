--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Sequences, Integers, TLC

VARIABLES rmState, onceSndPrepare, onceRcvCommit, onceRcvAbort, onceSilentAbort

vars == <<rmState, onceSndPrepare, onceRcvCommit, onceRcvAbort, onceSilentAbort>>

NextUnchanged == UNCHANGED vars

CONSTANT RMs

Symmetry == Permutations(RMs)

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ onceSndPrepare = [ rm \in RMs |-> FALSE]
/\ onceRcvCommit = [ rm \in RMs |-> FALSE]
/\ onceRcvAbort = [ rm \in RMs |-> FALSE]
/\ onceSilentAbort = [ rm \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ onceSndPrepare' = [onceSndPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvCommit, onceRcvAbort, onceSilentAbort>>

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ onceRcvCommit' = [onceRcvCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvAbort, onceSilentAbort>>

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceSilentAbort>>

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ onceSilentAbort' = [onceSilentAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort>>

OrigNext ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

OrigSpec == (Init /\ [][OrigNext]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ onceSndPrepare \in [RMs -> BOOLEAN]
/\ onceRcvCommit \in [RMs -> BOOLEAN]
/\ onceRcvAbort \in [RMs -> BOOLEAN]
/\ onceSilentAbort \in [RMs -> BOOLEAN]

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

SepAssumption ==
    /\ \A Var1 \in RMs : (onceRcvCommit[Var1]) => (onceSndPrepare[Var1])
    /\ (\E Var1 \in RMs : onceRcvCommit[Var1]) => (\A Var1 \in RMs : onceSndPrepare[Var1])
    /\ \A Var1 \in RMs : (onceRcvAbort[Var1]) => (\A Var0 \in RMs : ~(onceRcvCommit[Var0]))

Next == OrigNext /\ SepAssumption'
Spec == Init /\ [][Next]_vars


Inv223_1_0_def == \A rmi \in RMs : \A rmj \in RMs : (rmState[rmi] = "aborted") \/ (~(onceSilentAbort[rmi]))
Inv111_1_1_def == \A rmi \in RMs : \A rmj \in RMs : (onceRcvCommit[rmj]) \/ (~(rmState[rmj] = "committed"))
Inv242_1_2_def == \A rmi \in RMs : \A rmj \in RMs : (rmState[rmi] = "committed") \/ (~(onceRcvCommit[rmi]))
Inv415_1_3_def == \A rmi \in RMs : \A rmj \in RMs : ~(onceSilentAbort[rmi]) \/ (~(onceSndPrepare[rmi]))
Inv439_1_4_def == \A rmi \in RMs : \A rmj \in RMs : ~(onceSndPrepare[rmi]) \/ (~(rmState[rmi] = "working"))
Inv306_2_5_def == \A rmi \in RMs : \A rmj \in RMs : (onceRcvAbort[rmi]) \/ (~(onceSndPrepare[rmi])) \/ (~(rmState[rmi] = "aborted"))

\* The inductive invariant candidate.
IndAuto ==
  /\ Consistent
  /\ Inv223_1_0_def
  /\ Inv111_1_1_def
  /\ Inv242_1_2_def
  /\ Inv415_1_3_def
  /\ Inv439_1_4_def
  /\ Inv306_2_5_def

IISpec == TypeOK /\ IndAuto /\ [][Next /\ SepAssumption']_vars

=============================================================================
