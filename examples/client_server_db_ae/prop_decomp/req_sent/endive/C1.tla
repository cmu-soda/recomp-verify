--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES request_sent, response_received, Fluent1, Fluent0

vars == <<request_sent, response_received, Fluent1, Fluent0>>

NextUnchanged == UNCHANGED vars

Symmetry == Permutations(Node) \cup Permutations(Request) \cup Permutations(Response) \cup Permutations(DbRequestId)

CandSep ==
/\ \A var0 \in Node : (Fluent1[var0]) => (Fluent0[var0])

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<response_received>>
/\ UNCHANGED<<Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<request_sent,response_received>>
/\ Fluent1' = [Fluent1 EXCEPT![n] = FALSE]
/\ UNCHANGED<<Fluent0>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<request_sent>>
/\ Fluent0' = [Fluent0 EXCEPT![n] = FALSE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ request_sent = {}
/\ response_received = {}
/\ Fluent1 = [ x0 \in Node |-> TRUE]
/\ Fluent0 = [ x0 \in Node |-> TRUE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ Fluent1 \in [Node -> BOOLEAN]
/\ Fluent0 \in [Node -> BOOLEAN]

Safety == (\A n \in Node, p \in Response : (\E r \in Request : ((<<n,p>> \in response_received) => (<<n,r>> \in request_sent))))
=============================================================================
