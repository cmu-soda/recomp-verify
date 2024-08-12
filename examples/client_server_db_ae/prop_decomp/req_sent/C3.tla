--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES t

Node == {"n1","n2"}

Request == {"req1","req2"}

Response == {"resp1","resp2","resp3"}

DbRequestId == {"id1","id2"}

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
