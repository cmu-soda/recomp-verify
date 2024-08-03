--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES onceSilentAbort, onceRcvAbort, rmState, onceRcvCommit, onceSndPrepare

vars == <<onceSilentAbort, onceRcvAbort, rmState, onceRcvCommit, onceSndPrepare>>

CandSep ==
/\ \A var0 \in RMs : (onceRcvCommit[var0]) => (onceSndPrepare[var0])
/\ (\E var0 \in RMs : onceRcvCommit[var0]) => (\A var0 \in RMs : onceSndPrepare[var0])
/\ (\E var0 \in RMs : onceRcvAbort[var0]) => (~(\E var0 \in RMs : onceRcvCommit[var0]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ onceSilentAbort = [ x0 \in RMs |-> FALSE]
/\ onceRcvAbort = [ x0 \in RMs |-> FALSE]
/\ onceRcvCommit = [ x0 \in RMs |-> FALSE]
/\ onceSndPrepare = [ x0 \in RMs |-> FALSE]

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