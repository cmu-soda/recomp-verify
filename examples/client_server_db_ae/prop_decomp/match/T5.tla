--------------------------- MODULE T5 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

VARIABLES db_response_sent

Node == {"n1","n2"}

Request == {"req1","req2"}

Response == {"resp1","resp2","resp3"}

DbRequestId == {"id1","id2"}

vars == <<db_response_sent>>

DbProcessRequest(i,r,p) ==
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ UNCHANGED <<db_response_sent>>

Next ==
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))

Init ==
/\ db_response_sent = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
=============================================================================
