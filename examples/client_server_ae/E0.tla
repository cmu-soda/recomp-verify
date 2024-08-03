--------------------------- MODULE E0 ---------------------------

CONSTANTS Node, Request, Response

VARIABLES response_sent

vars == <<response_sent>>

Respond(n,r,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ UNCHANGED <<response_sent>>

Next ==
\/ (\E n \in Node, r \in Request, p \in Response : Respond(n,r,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ response_sent = {}

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (response_sent \in SUBSET((Node \X Response)))

NextUnchanged == UNCHANGED vars
=============================================================================
