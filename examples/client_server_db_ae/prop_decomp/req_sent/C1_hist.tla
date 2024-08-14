--------------------------- MODULE C1_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES request_sent, response_received, Fluent1, Fluent0

vars == <<request_sent, response_received, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Node : (Fluent0[var0]) => (Fluent1[var0])

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<response_received>>
/\ UNCHANGED<<Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<request_sent,response_received>>
/\ Fluent1' = [Fluent1 EXCEPT![n] = TRUE]
/\ UNCHANGED<<Fluent0>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<request_sent>>
/\ Fluent0' = [Fluent0 EXCEPT![n] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ request_sent = {}
/\ response_received = {}
/\ Fluent1 = [ x0 \in Node |-> FALSE]
/\ Fluent0 = [ x0 \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : (\E r \in Request : ((<<n,p>> \in response_received) => (<<n,r>> \in request_sent))))
=============================================================================
