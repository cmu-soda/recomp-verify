--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Sequences, Integers

VARIABLES tmState, tmPrepared,
    onceRcvPrepare, onceSndCommit, onceSndAbort

vars == <<tmState, tmPrepared, onceRcvPrepare, onceSndCommit, onceSndAbort>>

RMs == {"rm1","rm2"}

Message == ([type : {"Prepared"},theRM : RMs] \cup [type : {"Commit","Abort"}])

Init ==
/\ tmState = "init"
/\ tmPrepared = {}
/\ onceRcvPrepare = [ rm \in RMs |-> FALSE]
/\ onceSndCommit = [ rm \in RMs |-> FALSE]
/\ onceSndAbort = [ rm \in RMs |-> FALSE]

RcvPrepare(rm) ==
/\ tmState = "init"
/\ tmPrepared' = (tmPrepared \cup {rm})
/\ UNCHANGED <<tmState>>
/\ onceRcvPrepare' = [onceRcvPrepare EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceSndCommit, onceSndAbort>>

SndCommit(rm) ==
/\ (tmState \in {"init","commmitted"})
/\ tmState' = "committed"
/\ tmPrepared = RMs
/\ UNCHANGED <<tmPrepared>>
/\ onceSndCommit' = [onceSndCommit EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvPrepare, onceSndAbort>>

SndAbort(rm) ==
/\ (tmState \in {"init","aborted"})
/\ tmState' = "aborted"
/\ UNCHANGED <<tmPrepared>>
/\ onceSndAbort' = [onceSndAbort EXCEPT![rm] = TRUE]
/\ UNCHANGED<<onceRcvPrepare, onceSndCommit>>

Next ==
\E rm \in RMs :
\/ RcvPrepare(rm)
\/ SndCommit(rm)
\/ SndAbort(rm)

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (tmState \in {"init","committed","aborted"})
/\ (tmPrepared \in SUBSET(RMs))
/\ onceRcvPrepare \in [RMs -> BOOLEAN]
/\ onceSndCommit \in [RMs -> BOOLEAN]
/\ onceSndAbort \in [RMs -> BOOLEAN]


(*
SafetyActInv ==
    /\ once(\E rm \in RMs : SndCommit(rm)) => (\A rm \in RMs : ~SndAbort(rm))
    /\ once(\E rm \in RMs : SndAbort(rm)) => (\A rm \in RMs : ~SndCommit(rm))
    /\ (\E rm \in RMs : SndCommit(rm)) => once(\A rm \in RMs : RcvPrepare(rm))
*)

(*
\* this property doesn't work!! it's too strong, i.e. this module does not satisfy it
SafetyStateInv ==
    /\ (\E rm \in RMs : onceSndCommit[rm]) => (\A rm \in RMs : ~ENABLED SndAbort(rm))
    /\ (\E rm \in RMs : onceSndAbort[rm]) => (\A rm \in RMs : ~ENABLED SndCommit(rm))
    /\ (\E rm \in RMs : ENABLED SndCommit(rm)) => (\A rm \in RMs : onceRcvPrepare[rm])
*)

SafetyStateInv ==
    /\ (\E rm \in RMs : onceSndCommit[rm]) => (\A rm \in RMs : ~onceSndAbort[rm])
    /\ (\E rm \in RMs : onceSndAbort[rm]) => (\A rm \in RMs : ~onceSndCommit[rm])
    /\ (\E rm \in RMs : onceSndCommit[rm]) => (\A rm \in RMs : onceRcvPrepare[rm])


(*
\* IndInv version with ENABLED
IndInv ==
    /\ SafetyStateInv
    /\ (tmState = "committed") => ~(\E rm \in RMs : ENABLED SndAbort(rm))
    /\ (tmState = "committed") <=> (\E rm \in RMs : onceSndCommit[rm])
    /\ (tmState = "aborted") => ~(\E rm \in RMs : ENABLED SndCommit(rm))
    /\ (tmState = "aborted") <=> (\E rm \in RMs : onceSndAbort[rm])
    /\ \A rm \in RMs : rm \in tmPrepared <=> onceRcvPrepare[rm]
*)

(*
\* hand written IndInv
IndInv ==
    /\ SafetyStateInv
    /\ (tmState = "committed") => ~(\E rm \in RMs : (tmState \in {"init","aborted"}))
    /\ (tmState = "committed") <=> (\E rm \in RMs : onceSndCommit[rm])
    /\ (tmState = "aborted") => ~(\E rm \in RMs : (tmState \in {"init","commmitted"}) /\ tmPrepared = RMs)
    /\ (tmState = "aborted") <=> (\E rm \in RMs : onceSndAbort[rm])
    /\ \A rm \in RMs : rm \in tmPrepared <=> onceRcvPrepare[rm]
*)

\* Endive's IndInv
IndInv ==
    /\ SafetyStateInv
    /\ \A rmi \in RMs : \A rmj \in RMs : ~(onceSndAbort[rmi]) \/ (~(tmState = "init"))
    /\ \A rmi \in RMs : \A rmj \in RMs : (tmState = "committed") \/ (~(onceSndCommit[rmi]))
    /\ \A rmi \in RMs : \A rmj \in RMs : (onceRcvPrepare[rmi]) \/ (~(rmi \in tmPrepared))

IISpec == TypeOK /\ IndInv /\ [][Next]_vars

=============================================================================
