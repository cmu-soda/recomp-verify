--------------------------- MODULE E1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES tmState, tmPrepared, onceRcvPrepare, onceSndCommit, onceSndAbort

vars == <<tmState, tmPrepared, onceRcvPrepare, onceSndCommit, onceSndAbort>>

CandSep ==
TRUE

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ onceRcvPrepare = [ x0 \in RMs |-> FALSE]
/\ onceSndCommit = [ x0 \in RMs |-> FALSE]
/\ onceSndAbort = [ x0 \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ onceRcvPrepare' = [onceRcvPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndCommit, onceSndAbort>>
/\ CandSep'

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared>>
/\ onceSndCommit' = [onceSndCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvPrepare, onceSndAbort>>
/\ CandSep'

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ onceSndAbort' = [onceSndAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvPrepare, onceSndCommit>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))

Safety ==
/\ \A V \in RMs : (onceSndCommit[V]) => (onceRcvPrepare[V])
/\ \A V \in RMs : \A W \in RMs : (onceSndCommit[V]) => (onceRcvPrepare[W])
/\ \A V \in RMs : (onceSndAbort[V]) => (~(onceSndCommit[V]))
/\ \A V \in RMs : (onceSndCommit[V]) => (\A W \in RMs : ~(onceSndAbort[W]))
=============================================================================
