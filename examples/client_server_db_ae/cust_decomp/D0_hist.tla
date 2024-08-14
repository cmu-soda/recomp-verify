--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES t, request_sent, Fluent6, response_sent, Fluent5, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0

vars == <<t, request_sent, Fluent6, response_sent, Fluent5, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Response : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in Request : (Fluent3[var0]) => (Fluent2[var0])
/\ \A var0 \in DbRequestId : \E var1 \in Request : Fluent4[var1][var0]
/\ \A var0 \in DbRequestId : (Fluent6[var0]) => (Fluent5[var0])

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received,t>>
/\ UNCHANGED<<Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent6' = [Fluent6 EXCEPT![i] = FALSE]
/\ Fluent5' = [Fluent5 EXCEPT![i] = FALSE]
/\ Fluent4' = [Fluent4 EXCEPT![r][i] = FALSE]
/\ Fluent2' = [Fluent2 EXCEPT![r] = TRUE]
/\ UNCHANGED<<Fluent3, Fluent1, Fluent0>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received,t>>
/\ Fluent5' = [Fluent5 EXCEPT![i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![r][i] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![r] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![p] = FALSE]
/\ UNCHANGED<<Fluent6, Fluent2, Fluent0>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,n>> \in t)
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received,t>>
/\ Fluent6' = [Fluent6 EXCEPT![i] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![p] = FALSE]
/\ UNCHANGED<<Fluent5, Fluent4, Fluent3, Fluent2, Fluent1>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent,t>>
/\ UNCHANGED<<Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))
/\ request_sent = {}
/\ response_sent = {}
/\ response_received = {}
/\ t = {}
/\ Fluent6 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent5 = [ x0 \in DbRequestId |-> TRUE]
/\ Fluent4 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent3 = [ x0 \in Request |-> FALSE]
/\ Fluent2 = [ x0 \in Request |-> FALSE]
/\ Fluent1 = [ x0 \in Response |-> TRUE]
/\ Fluent0 = [ x0 \in Response |-> TRUE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
