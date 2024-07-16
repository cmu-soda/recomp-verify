--------------------------- MODULE C1_vars ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES rmState, onceSndPrepare, onceRcvCommit, onceRcvAbort, onceSilentAbort

vars == <<rmState, onceSndPrepare, onceRcvCommit, onceRcvAbort, onceSilentAbort>>

RMs == {"rm1","rm2"}

\* Neg trace check
CandSep ==
    /\ (\E Var1 \in RMs : onceRcvCommit[Var1]) => (\A Var1 \in RMs : onceSndPrepare[Var1])
    /\ (\E Var1 \in RMs : onceRcvAbort[Var1]) => (\A Var1 \in RMs : ~(onceRcvCommit[Var1]))

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
/\ CandSep'

RcvCommit(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "committed"]
/\ onceRcvCommit' = [onceRcvCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvAbort, onceSilentAbort>>
/\ CandSep'

RcvAbort(rm) ==
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ onceRcvAbort' = [onceRcvAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceSilentAbort>>
/\ CandSep'

SilentAbort(rm) ==
/\ rmState[rm] = "working"
/\ rmState' = [rmState EXCEPT![rm] = "aborted"]
/\ onceSilentAbort' = [onceSilentAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndPrepare, onceRcvCommit, onceRcvAbort>>
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
/\ onceSndPrepare \in [RMs -> BOOLEAN]
/\ onceRcvCommit \in [RMs -> BOOLEAN]
/\ onceRcvAbort \in [RMs -> BOOLEAN]
/\ onceSilentAbort \in [RMs -> BOOLEAN]

Consistent == (\A rm1,rm2 \in RMs : ~((rmState[rm1] = "aborted" /\ rmState[rm2] = "committed")))

(*
WA ==
    /\ (\E rm \in RMs : RcvCommit(rm)) => (\A rm \in RMs : ~RcvAbort(rm))
    /\ (\E rm \in RMs : RcvAbort(rm)) => (\A rm \in RMs : ~RcvCommit(rm))

    \* really what WA should be:
    \*/\ (\E rm \in RMs : RcvCommit(rm)) => [](\A rm \in RMs : ~RcvAbort(rm))
    \*/\ (\E rm \in RMs : RcvAbort(rm)) => [](\A rm \in RMs : ~RcvCommit(rm))
    \*/\ (\E rm \in RMs : RcvCommit(rm)) => (\A rm \in RMs : once(SndPrepare(rm)))

\* Spec (the RM spec) with the assumptions in WA
WASpec == Init /\ [][Next /\ WA]_vars
*)

(*
\* WA restated as an invariant, using PTL
WAInv ==
    /\ \E rm \in RMs : once(RcvCommit(rm)) => (\A rm \in RMs : ~RcvAbort(rm))
    /\ \E rm \in RMs : once(RcvAbort(rm)) => (\A rm \in RMs : ~RcvCommit(rm))
    /\ (\E rm \in RMs : RcvCommit(rm)) => (\A rm \in RMs : once(SndPrepare(rm)))
*)

WAStateInv ==
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : ~RcvAbort(rm))
    /\ (\E rm \in RMs : onceRcvAbort[rm]) => (\A rm \in RMs : ~RcvCommit(rm))
    /\ (\E rm \in RMs : RcvCommit(rm)) => (\A rm \in RMs : onceSndPrepare[rm])

\*CandSpec == Init /\ [][Next /\ CandSep]_vars
CandSpec == Spec

\* Spec (the RM spec) with the assumptions in WA
WASpec == Init /\ [][Next /\ WAStateInv]_vars


(*
\* hand written IndInv
IndInv ==
    /\ Consistent

    \* committed is the result of RcvCommit(rm)
    /\ \A rm \in RMs : (rmState[rm] = "committed") => onceRcvCommit[rm]
    \* if \E rm : ENABLED RcvCommit(rm), then ...
    /\ (\E rm \in RMs : onceRcvCommit[rm]) => (\A rm \in RMs : rmState[rm] \in {"prepared","committed"})
    
    \* prepared invariant for the RMs
    \*/\ \A rm \in RMs : (rmState[rm] \in {"prepared","committed"}) => onceSndPrepare[rm]
    /\ \A rm \in RMs : onceSndPrepare[rm] => (rmState[rm] # "working")
    
    \* abort invariant for the RMs
    /\ (\E rm \in RMs : rmState[rm] = "aborted" /\ onceSndPrepare[rm]) => (\E rm \in RMs : onceRcvAbort[rm])
*)

\* Endive's IndInv
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

IISpec == TypeOK /\ IndInv /\ [][Next /\ WAStateInv]_vars

=============================================================================
