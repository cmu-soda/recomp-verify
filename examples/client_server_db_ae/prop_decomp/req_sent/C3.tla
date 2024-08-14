--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES t

vars == <<t>>

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,n>> \in t)
/\ UNCHANGED <<t>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ t = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (t \in SUBSET((DbRequestId \X Node)))
=============================================================================
