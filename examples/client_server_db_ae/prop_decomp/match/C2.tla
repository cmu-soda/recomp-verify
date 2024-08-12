--------------------------- MODULE C2 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES db_request_sent

Node == {"n1","n2"}

Request == {"req1","req2"}

Response == {"resp1","resp2","resp3"}

DbRequestId == {"id1","id2"}

vars == <<db_request_sent>>

ServerProcessRequest(n,r,i) ==
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ UNCHANGED <<db_request_sent>>

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))

Init ==
/\ db_request_sent = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
=============================================================================
