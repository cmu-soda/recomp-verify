--------------------------- MODULE C4 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES response_sent

vars == <<response_sent>>

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ UNCHANGED <<response_sent>>

Next ==
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ response_sent = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (response_sent \in SUBSET((Node \X Response)))
=============================================================================
