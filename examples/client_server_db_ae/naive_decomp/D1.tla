--------------------------- MODULE D1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent

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
