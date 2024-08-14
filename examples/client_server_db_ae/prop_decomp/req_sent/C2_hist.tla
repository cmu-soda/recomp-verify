--------------------------- MODULE C2_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, Fluent1, Fluent0

vars == <<db_request_sent, Fluent1, Fluent0>>

CandSep ==
TRUE

ServerProcessRequest(n,r,i) ==
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent1' = [Fluent1 EXCEPT![n] = TRUE]
/\ UNCHANGED<<Fluent0>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ UNCHANGED <<db_request_sent>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent1, Fluent0>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))

Init ==
/\ db_request_sent = {}
/\ Fluent1 = [ x0 \in Node |-> FALSE]
/\ Fluent0 = [ x0 \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))

Safety ==
/\ \A var0 \in Node : (Fluent0[var0]) => (Fluent1[var0])
=============================================================================
