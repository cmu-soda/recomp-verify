--------------------------- MODULE C4 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES request_sent

Node == {"n1","n2"}

Request == {"req1","req2"}

Response == {"resp1","resp2","resp3"}

DbRequestId == {"id1","id2"}

vars == <<request_sent>>

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<request_sent>>

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))

Init ==
/\ request_sent = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (request_sent \in SUBSET((Node \X Request)))
=============================================================================
