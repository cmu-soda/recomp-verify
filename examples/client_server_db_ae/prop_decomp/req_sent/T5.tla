--------------------------- MODULE T5 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_response_sent

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
