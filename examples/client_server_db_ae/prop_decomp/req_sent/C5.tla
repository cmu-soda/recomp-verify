--------------------------- MODULE C5 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES match

Node == {"n1","n2"}

Request == {"req1","req2"}

Response == {"resp1","resp2","resp3"}

DbRequestId == {"id1","id2"}

vars == <<match>>

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match>>

Next ==
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
=============================================================================
