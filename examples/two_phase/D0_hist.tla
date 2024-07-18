--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES onceSilentAbort, onceRcvAbort, rmState, onceRcvCommit, onceSndPrepare

vars == <<onceSilentAbort, onceRcvAbort, rmState, onceRcvCommit, onceSndPrepare>>

RMs == {"rm1","rm2"}

CandSep == (\A Var1 \in RMs : (onceRcvCommit[Var1]) => (onceSndPrepare[Var1])) /\ ((\E Var1 \in RMs : onceRcvCommit[Var1]) => (\A Var1 \in RMs : onceSndPrepare[Var1])) /\ (\A Var1 \in RMs : (onceRcvAbort[Var1]) => (\A Var0 \in RMs : ~(onceRcvCommit[Var0])))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ onceSilentAbort = [ rm \in RMs |-> FALSE]
/\ onceRcvAbort = [ rm \in RMs |-> FALSE]
/\ onceRcvCommit = [ rm \in RMs |-> FALSE]
/\ onceSndPrepare = [ rm \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ onceSndPrepare' = [onceSndPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvCommit>>
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ onceRcvCommit' = [onceRcvCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceSndPrepare>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvCommit, onceSndPrepare>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ onceSilentAbort' = [onceSilentAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvAbort, onceRcvCommit, onceSndPrepare>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvCommit(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
