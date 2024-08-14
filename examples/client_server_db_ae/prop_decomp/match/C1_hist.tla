--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES match, response_received, Fluent1, Fluent0

vars == <<match, response_received, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Response : (Fluent1[var0]) => (Fluent0[var0])

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,response_received>>
/\ Fluent1' = [Fluent1 EXCEPT![p] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![p] = TRUE]
/\ UNCHANGED<<>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match>>
/\ Fluent1' = [Fluent1 EXCEPT![p] = TRUE]
/\ UNCHANGED<<Fluent0>>
/\ CandSep'

Next ==
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))
/\ response_received = {}
/\ Fluent1 = [ x0 \in Response |-> FALSE]
/\ Fluent0 = [ x0 \in Response |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : (\E r \in Request : ((<<n,p>> \in response_received) => (<<r,p>> \in match))))
=============================================================================
