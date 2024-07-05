--------------------------- MODULE TPC ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES rmState, msgs, tmState, tmPrepared,
    onceSndPrepare, onceRcvCommit, onceRcvAbort,
    onceRcvPrepare, onceSndCommit, onceSndAbort,
    onceSilentAbort

vars == <<rmState, msgs, tmState, tmPrepared, onceSndPrepare, onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort, onceSilentAbort>>

RMs == {"rm1","rm2"}

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ rmState = [rm \in RMs |-> "working"]
/\ msgs = {}
/\ tmState = "init"
/\ tmPrepared = {}
/\ onceSndPrepare = [ rm \in RMs |-> FALSE]
/\ onceRcvCommit = [ rm \in RMs |-> FALSE]
/\ onceRcvAbort = [ rm \in RMs |-> FALSE]
/\ onceRcvPrepare = [ rm \in RMs |-> FALSE]
/\ onceSndCommit = [ rm \in RMs |-> FALSE]
/\ onceSndAbort = [ rm \in RMs |-> FALSE]
/\ onceSilentAbort = [ rm \in RMs |-> FALSE]

SndPrepare(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "prepared"]
/\ msgs' = (msgs \cup {[type |-> "Prepared",theRM |-> rm]})
/\ UNCHANGED<<tmState, tmPrepared>>
/\ onceSndPrepare' = [onceSndPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort, onceSilentAbort>>

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ ([type |-> "Prepared",theRM |-> rm] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<rmState>>
/\ onceRcvPrepare' = [onceRcvPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort, onceSndCommit, onceSndAbort, onceSilentAbort>>

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmState' = "committed"
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>
/\ msgs' = (msgs \cup {[type |-> "Commit"]})
/\ UNCHANGED<<rmState>>
/\ onceSndCommit' = [onceSndCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndAbort, onceSilentAbort>>

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ ([type |-> "Commit"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<tmState, tmPrepared>>
/\ onceRcvCommit' = [onceRcvCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort, onceSilentAbort>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ msgs' = (msgs \cup {[type |-> "Abort"]})
/\ UNCHANGED<<rmState>>
/\ onceSndAbort' = [onceSndAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSilentAbort>>

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ ([type |-> "Abort"] \in msgs)
/\ UNCHANGED <<msgs>>
/\ UNCHANGED<<tmState, tmPrepared>>
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvPrepare, onceSndCommit, onceSndAbort, onceSilentAbort>>

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ UNCHANGED<<msgs, tmState, tmPrepared>>
/\ onceSilentAbort' = [onceSilentAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort, onceRcvPrepare, onceSndCommit, onceSndAbort>>

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
/\ (rmState \in [RMs -> {"working","prepared","committed","aborted"}])
/\ (msgs \in SUBSET(Message))
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ onceSndPrepare \in [RMs -> BOOLEAN]
/\ onceRcvCommit \in [RMs -> BOOLEAN]
/\ onceRcvAbort \in [RMs -> BOOLEAN]
/\ onceRcvPrepare \in [RMs -> BOOLEAN]
/\ onceSndCommit \in [RMs -> BOOLEAN]
/\ onceSndAbort \in [RMs -> BOOLEAN]
/\ onceSilentAbort \in [RMs -> BOOLEAN]

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))


SafetyStateInvC2 ==
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : ~onceRcvAbort[rm])
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\A rm \in RMs : ~onceRcvCommit[rm])
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : onceSndPrepare[rm])

SafetyStateInvC3 ==
    /\ (\E rm \in RMs : onceSndCommit[rm]) => (\A rm \in RMs : ~onceSndAbort[rm])
    /\ (\E rm \in RMs : onceSndAbort[rm]) => (\A rm \in RMs : ~onceSndCommit[rm])
    /\ (\E rm \in RMs : onceSndCommit[rm]) => (\A rm \in RMs : onceRcvPrepare[rm])

(*
\* IndInv version with ENABLED
IndInv ==
    /\ Consistent
    /\ \A rm \in RMs : (rmState[rm] = "committed") => onceRcvCommit[rm]
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : rmState[rm] \in {"prepared","committed"})
    /\ \A rm \in RMs : onceSndPrepare[rm] => (rmState[rm] # "working")
    /\ (\E rm \in RMs : rmState[rm] = "aborted" /\ onceSndPrepare[rm]) => (\E rm \in RMs : onceRcvAbort[rm])

    /\ SafetyStateInvC2
    (*****************************************************************)
    \*/\ \A rm \in RMs : ENABLED RcvPrepare(rm) <=>  onceSndPrepare[rm]
    /\ \A rm \in RMs : ENABLED RcvPrepare(rm) =>  onceSndPrepare[rm]
    (*****************************************************************)
    /\ (\E rm \in RMs : ENABLED RcvCommit(rm)) => (\E rm \in RMs : onceSndCommit[rm])
    /\ (\E rm \in RMs : ENABLED RcvAbort(rm)) => (\E rm \in RMs : onceSndAbort[rm])
    /\ \A rm \in RMs : onceRcvPrepare[rm] => onceSndPrepare[rm]
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\E rm \in RMs : onceSndCommit[rm])
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\E rm \in RMs : onceSndAbort[rm])
    /\ ~([type |-> "Commit"] \in msgs /\ [type |-> "Abort"] \in msgs)
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : ~ENABLED RcvAbort(rm))
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\A rm \in RMs : ~ENABLED RcvCommit(rm))
    /\ (\E rm \in RMs : ENABLED RcvCommit(rm)) => (\A rm \in RMs : onceSndPrepare[rm])

    /\ SafetyStateInvC3
    /\ (tmState = "committed") => ~(\E rm \in RMs : ENABLED SndAbort(rm))
    /\ (tmState = "committed") <=> (\E rm \in RMs : onceSndCommit[rm])
    /\ (tmState = "aborted") => ~(\E rm \in RMs : ENABLED SndCommit(rm))
    /\ (tmState = "aborted") <=> (\E rm \in RMs : onceSndAbort[rm])
    /\ \A rm \in RMs : rm \in tmPrepared <=> onceRcvPrepare[rm]
*)

(*
\* hand written IndInv's
IndInv ==
    /\ Consistent
    /\ \A rm \in RMs : (rmState[rm] = "committed") => onceRcvCommit[rm]
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : rmState[rm] \in {"prepared","committed"})
    /\ \A rm \in RMs : onceSndPrepare[rm] => (rmState[rm] # "working")
    /\ (\E rm \in RMs : rmState[rm] = "aborted" /\ onceSndPrepare[rm]) => (\E rm \in RMs : onceRcvAbort[rm])

    \*/\ SafetyStateInvC2
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

    \*/\ SafetyStateInvC3
    /\ (tmState = "committed") => ~(\E rm \in RMs : (tmState \in {"init","aborted"}))
    /\ (tmState = "committed") <=> (\E rm \in RMs : onceSndCommit[rm])
    /\ (tmState = "aborted") => ~(\E rm \in RMs : (tmState \in {"init","commmitted"}) /\ tmPrepared = RMs)
    /\ (tmState = "aborted") <=> (\E rm \in RMs : onceSndAbort[rm])
    /\ \A rm \in RMs : rm \in tmPrepared <=> onceRcvPrepare[rm]
*)

\* IndInv's from Endive
IndInv ==
    /\ Consistent
    /\ \A rmi \in RMs : \A rmj \in RMs : (onceSndPrepare[rmi]) \/ (~(rmState[rmj] = "committed"))
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceSilentAbort[rmi]) \/ (~(onceSndPrepare[rmi]))
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceRcvCommit[rmi]) \/ (~(rmState[rmj] = "working"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (onceRcvCommit[rmj]) \/ (~(rmState[rmj] = "committed"))
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceRcvCommit[rmi]) \/ (~(rmState[rmj] = "aborted"))
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceSndPrepare[rmi]) \/ (~(rmState[rmi] = "working"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (onceRcvAbort[rmi]) \/ (~(onceSndPrepare[rmi])) \/ (~(rmState[rmi] = "aborted"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (rmState[rmi] = "aborted") \/ (~(onceSilentAbort[rmi]))

    /\ SafetyStateInvC2
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

    /\ SafetyStateInvC3
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceSndAbort[rmi]) \/ (~(tmState = "init"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~(onceSndCommit[rmi]))
    /\ \A rmi \in RMs : \A rmj \in RMs : (onceRcvPrepare[rmi]) \/ (~(rmi \in tmPrepared))

IISpec == TypeOK /\ IndInv /\ [][Next]_vars


InitImpliesIndInv == Init => IndInv

=============================================================================
