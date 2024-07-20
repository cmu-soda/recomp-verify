--------------------------- MODULE TwoPhase_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, tmState, onceSilentAbort, onceRcvAbort, tmPrepared, rmState, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare

vars == <<msgs, tmState, onceSilentAbort, onceRcvAbort, tmPrepared, rmState, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

CandSep ==
\A V \in RMs : (onceRcvCommit[V]) => (\A W \in RMs : ~(onceRcvAbort[W]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ rmState = [rm \in RMs |-> "working"]
/\ tmState = "init"
/\ tmPrepared = {}
/\ onceSilentAbort = [ x0 \in RMs |-> FALSE]
/\ onceRcvAbort = [ x0 \in RMs |-> FALSE]
/\ onceRcvPrepare = [ x0 \in RMs |-> FALSE]
/\ onceRcvCommit = [ x0 \in RMs |-> FALSE]
/\ onceSndCommit = [ x0 \in RMs |-> FALSE]
/\ onceSndAbort = [ x0 \in RMs |-> FALSE]
/\ onceSndPrepare = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ UNCHANGED <<tmState,tmPrepared>>
/\ onceSndPrepare' = [onceSndPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<msgs,tmState,rmState>>
/\ onceRcvPrepare' = [onceRcvPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ (tmState \in {"init","commmitted"})
/\ tmPrepared = RMs
/\ tmState' = "committed"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ onceSndCommit' = [onceSndCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndAbort, onceSndPrepare>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ onceRcvCommit' = [onceRcvCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort, onceSndPrepare>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared,rmState>>
/\ onceSndAbort' = [onceSndAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndPrepare>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<msgs,tmState,tmPrepared>>
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSilentAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED <<tmState,tmPrepared,msgs>>
/\ onceSilentAbort' = [onceSilentAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)
\/ SilentAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))
=============================================================================
