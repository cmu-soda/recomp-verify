--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES request_sent, response_received

vars == <<request_sent,response_received>>

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<response_received>>

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<request_sent,response_received>>

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<request_sent>>

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ request_sent = {}
/\ response_received = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : (\E r \in Request : ((<<n,p>> \in response_received) => (<<n,r>> \in request_sent))))
=============================================================================
