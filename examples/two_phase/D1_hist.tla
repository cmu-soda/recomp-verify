--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, Integers

CONSTANTS RMs

VARIABLES msgs, onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare

vars == <<msgs, onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>

CandSep ==
/\ \A var1 \in RMs : (onceSndCommit[var1]) => (onceRcvPrepare[var1])
/\ \A var0 \in RMs : \A var1 \in RMs : (onceSndCommit[var0]) => (onceRcvPrepare[var1])
/\ \A var1 \in RMs : (onceSndCommit[var1]) => (~(onceSndAbort[var1]))
/\ (\E var1 \in RMs : onceSndAbort[var1]) => (\A var1 \in RMs : ~(onceSndCommit[var1]))

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ onceRcvAbort = [ x0 \in RMs |-> FALSE]
/\ onceRcvPrepare = [ x0 \in RMs |-> FALSE]
/\ onceRcvCommit = [ x0 \in RMs |-> FALSE]
/\ onceSndCommit = [ x0 \in RMs |-> FALSE]
/\ onceSndAbort = [ x0 \in RMs |-> FALSE]
/\ onceSndPrepare = [ x0 \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ onceSndPrepare' = [onceSndPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort>>
/\ CandSep'

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ onceRcvPrepare' = [onceRcvPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvAbort, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>
/\ CandSep'

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ onceSndCommit' = [onceSndCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndAbort, onceSndPrepare>>
/\ CandSep'

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ onceRcvCommit' = [onceRcvCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort, onceSndPrepare>>
/\ CandSep'

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ onceSndAbort' = [onceSndAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvAbort, onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndPrepare>>
/\ CandSep'

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvPrepare, onceRcvCommit, onceSndCommit, onceSndAbort, onceSndPrepare>>
/\ CandSep'

Next ==
\E rm \in RMs :
\/ SndPrepare(rm)
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ RcvCommit(rm)
\/ SndAbort(rm)
\/ RcvAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (msgs \in SUBSET(Message))

Safety ==
/\ \A V \in RMs : (onceRcvCommit[V]) => (onceSndPrepare[V])
/\ \A W \in RMs : \A V \in RMs : (onceRcvCommit[W]) => (onceSndPrepare[V])
/\ \A V \in RMs : (onceRcvCommit[V]) => (\A W \in RMs : ~(onceRcvAbort[W]))
=============================================================================
