--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent7, request_sent, Fluent6, Fluent5, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0

vars == <<Fluent7, request_sent, Fluent6, Fluent5, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Response : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in Request : (Fluent3[var0]) => (Fluent2[var0])
/\ \A var0 \in DbRequestId : (Fluent4[var0]) => (Fluent5[var0])
/\ \A var0 \in Node : (Fluent7[var0]) => (Fluent6[var0])

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_received>>
/\ UNCHANGED<<Fluent7, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent6' = [Fluent6 EXCEPT![n] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT![i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![i] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![r] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![r] = TRUE]
/\ UNCHANGED<<Fluent7, Fluent1, Fluent0>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent5' = [Fluent5 EXCEPT![i] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![r] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![p] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![p] = TRUE]
/\ UNCHANGED<<Fluent7, Fluent6, Fluent4, Fluent2>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent>>
/\ Fluent7' = [Fluent7 EXCEPT![n] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![p] = TRUE]
/\ UNCHANGED<<Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent0>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))
/\ request_sent = {}
/\ response_received = {}
/\ Fluent7 = [ x0 \in Node |-> FALSE]
/\ Fluent6 = [ x0 \in Node |-> FALSE]
/\ Fluent5 = [ x0 \in DbRequestId |-> TRUE]
/\ Fluent4 = [ x0 \in DbRequestId |-> TRUE]
/\ Fluent3 = [ x0 \in Request |-> FALSE]
/\ Fluent2 = [ x0 \in Request |-> FALSE]
/\ Fluent1 = [ x0 \in Response |-> FALSE]
/\ Fluent0 = [ x0 \in Response |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
