--------------------------- MODULE C2 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES msgs,
    onceSndPrepare, onceRcvCommit, onceRcvAbort,
    onceRcvPrepare, onceSndCommit, onceSndAbort

vars == <<msgs, onceSndPrepare, onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort>>

RMs == {"rm1","rm2"}

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ msgs = {}
/\ onceSndPrepare = [ rm \in RMs |-> FALSE]
/\ onceRcvCommit = [ rm \in RMs |-> FALSE]
/\ onceRcvAbort = [ rm \in RMs |-> FALSE]
/\ onceRcvPrepare = [ rm \in RMs |-> FALSE]
/\ onceSndCommit = [ rm \in RMs |-> FALSE]
/\ onceSndAbort = [ rm \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ onceSndPrepare' = [onceSndPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort>>

RcvPrepare(rm) ==
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ onceRcvPrepare' = [onceRcvPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort, onceSndCommit, onceSndAbort>>

SndCommit(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ onceSndCommit' = [onceSndCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndAbort>>

RcvCommit(rm) ==
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ onceRcvCommit' = [onceRcvCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort>>

SndAbort(rm) ==
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ onceSndAbort' = [onceSndAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndCommit>>

RcvAbort(rm) ==
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvPrepare, onceSndCommit, onceSndAbort>>

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
/\ onceSndPrepare \in [RMs -> BOOLEAN]
/\ onceRcvCommit \in [RMs -> BOOLEAN]
/\ onceRcvAbort \in [RMs -> BOOLEAN]
/\ onceRcvPrepare \in [RMs -> BOOLEAN]
/\ onceSndCommit \in [RMs -> BOOLEAN]
/\ onceSndAbort \in [RMs -> BOOLEAN]

(*
SafetyAct ==
    /\ (\E rm \in RMs : RcvCommit(rm)) => (\A rm \in RMs : ~RcvAbort(rm))
    /\ (\E rm \in RMs : RcvAbort(rm)) => (\A rm \in RMs : ~RcvCommit(rm))

    \* really what SafetyAct should be:
    \*/\ (\E rm \in RMs : RcvCommit(rm)) => [](\A rm \in RMs : ~RcvAbort(rm))
    \*/\ (\E rm \in RMs : RcvAbort(rm)) => [](\A rm \in RMs : ~RcvCommit(rm))

SafetyState ==
    /\ ([type |-> "Commit"] \in msgs) => ~([type |-> "Abort"] \in msgs)
    /\ ([type |-> "Abort"] \in msgs) => ~([type |-> "Commit"] \in msgs)

    \* really what SafetyState should be:
    \*/\ ([type |-> "Commit"] \in msgs) => []~([type |-> "Abort"] \in msgs)
    \*/\ ([type |-> "Abort"] \in msgs) => []~([type |-> "Commit"] \in msgs)
*)

(*
SafetyActInv ==
    /\ once(\E rm \in RMs : RcvCommit(rm)) => (\A rm \in RMs : ~RcvAbort(rm))
    /\ once(\E rm \in RMs : RcvAbort(rm)) => (\A rm \in RMs : ~RcvCommit(rm))
    /\ (\E rm \in RMs : RcvCommit(rm)) => (\A rm \in RMs : once(SndPrepare(rm)))
*)

(*
\* old version that used ENABLED
SafetyStateInv ==
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : ~ENABLED RcvAbort(rm))
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\A rm \in RMs : ~ENABLED RcvCommit(rm))
    /\ (\E rm \in RMs : ENABLED RcvCommit(rm)) => (\A rm \in RMs : onceSndPrepare[rm])
*)

SafetyStateInv ==
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : ~onceRcvAbort[rm])
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\A rm \in RMs : ~onceRcvCommit[rm])
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : onceSndPrepare[rm])


(*
\* WA stated as an invariant, using PTL
WAInv ==
    /\ once(\E rm \in RMs : SndCommit(rm)) => (\A rm \in RMs : ~SndAbort(rm))
    /\ once(\E rm \in RMs : SndAbort(rm)) => (\A rm \in RMs : ~SndCommit(rm))
    /\ (\E rm \in RMs : SndCommit(rm)) => once(\A rm \in RMs : RcvPrepare(rm))
*)

WAStateInv ==
    /\ (\E rm \in RMs : onceSndCommit[rm]) => (\A rm \in RMs : ~SndAbort(rm))
    /\ (\E rm \in RMs : onceSndAbort[rm]) => (\A rm \in RMs : ~SndCommit(rm))
    /\ (\E rm \in RMs : SndCommit(rm)) => (\A rm \in RMs : onceRcvPrepare[rm])

\* Spec (the RM spec) with the assumptions in WA
WASpec == Init /\ [][Next /\ WAStateInv]_vars


(*
\* II for the old SafetyStateInv that used ENABLED
IndInv ==
    /\ SafetyStateInv
    /\ \A rm \in RMs : ENABLED RcvPrepare(rm) <=>  onceSndPrepare[rm]
    /\ (\E rm \in RMs : ENABLED RcvCommit(rm)) => (\E rm \in RMs : onceSndCommit[rm])
    /\ (\E rm \in RMs : ENABLED RcvAbort(rm)) => (\E rm \in RMs : onceSndAbort[rm])
    /\ \A rm \in RMs : onceRcvPrepare[rm] => onceSndPrepare[rm]
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\E rm \in RMs : onceSndCommit[rm])
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\E rm \in RMs : onceSndAbort[rm])
    /\ ~([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)
*)

(*
\* IndInv version with ENABLED
IndInv ==
    /\ SafetyStateInv
    /\ \A rm \in RMs : ENABLED RcvPrepare(rm) <=>  onceSndPrepare[rm]
    /\ (\E rm \in RMs : ENABLED RcvCommit(rm)) => (\E rm \in RMs : onceSndCommit[rm])
    /\ (\E rm \in RMs : ENABLED RcvAbort(rm)) => (\E rm \in RMs : onceSndAbort[rm])
    /\ \A rm \in RMs : onceRcvPrepare[rm] => onceSndPrepare[rm]
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\E rm \in RMs : onceSndCommit[rm])
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\E rm \in RMs : onceSndAbort[rm])
    /\ ~([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : ~ENABLED RcvAbort(rm))
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\A rm \in RMs : ~ENABLED RcvCommit(rm))
    /\ (\E rm \in RMs : ENABLED RcvCommit(rm)) => (\A rm \in RMs : onceSndPrepare[rm])
*)

(*
\* hand written IndInv
IndInv ==
    /\ SafetyStateInv
    /\ \A rm \in RMs : ([type |-> "Prepared",theRM |-> rm] \in msgs) <=>  onceSndPrepare[rm]
    /\ (\E rm \in RMs : ([type |-> "Commit"] \in msgs)) => (\E rm \in RMs : onceSndCommit[rm])
    /\ (\E rm \in RMs : ([type |-> "Abort"] \in msgs)) => (\E rm \in RMs : onceSndAbort[rm])
    /\ \A rm \in RMs : onceRcvPrepare[rm] => onceSndPrepare[rm]
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\E rm \in RMs : onceSndCommit[rm])
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\E rm \in RMs : onceSndAbort[rm])
    /\ ~([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : ~([type |-> "Abort"] \in msgs))
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\A rm \in RMs : ~([type |-> "Commit"] \in msgs))
    /\ (\E rm \in RMs : ([type |-> "Commit"] \in msgs)) => (\A rm \in RMs : onceSndPrepare[rm])
*)

\* Endive's IndInv
IndInv ==
    /\ SafetyStateInv
    /\ \E rmi \in RMs : \A rmj \in RMs : ~([type |-> "Commit"] \in msgs) \/ (~(onceSndAbort[rmj]))
    /\ \E rmi \in RMs : \A rmj \in RMs : ~([type |-> "Abort"] \in msgs) \/ (~(onceSndCommit[rmj]))
    /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndAbort[rmi]) \/ (~(onceRcvAbort[rmj]))
    /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndCommit[rmi]) \/ (~(onceRcvCommit[rmj]))
    /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndPrepare[rmj]) \/ (~([type |-> "Commit"] \in msgs))
    /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndAbort[rmi]) \/ (~([type |-> "Abort"] \in msgs))
    /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndCommit[rmi]) \/ (~([type |-> "Commit"] \in msgs))
    /\ \E rmi \in RMs : \A rmj \in RMs : ([type |-> "Commit"] \in msgs) \/ (~(onceSndCommit[rmj]))
    /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndPrepare[rmj]) \/ (~(onceRcvPrepare[rmj]))
    /\ \E rmi \in RMs : \A rmj \in RMs : (onceSndPrepare[rmj]) \/ (~([type |-> "Prepared", theRM |-> rmj] \in msgs))

IISpec == TypeOK /\ IndInv /\ [][Next /\ WAStateInv]_vars


InitImpliesIndInv == Init => IndInv

=============================================================================
