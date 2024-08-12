--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent11, Fluent9, Fluent8, Fluent7, request_sent, Fluent6, response_sent, Fluent5, Fluent10, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0

vars == <<Fluent11, Fluent9, Fluent8, Fluent7, request_sent, Fluent6, response_sent, Fluent5, Fluent10, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in DbRequestId : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in Response : (Fluent3[var0]) => (Fluent2[var0])
/\ \A var0 \in DbRequestId : \E var1 \in Node : Fluent4[var0][var1]
/\ \A var0 \in Request : (Fluent5[var0]) => (Fluent6[var0])
/\ \A var0 \in DbRequestId : \E var1 \in Request : Fluent7[var1][var0]
/\ \A var0 \in DbRequestId : (Fluent8[var0]) => (Fluent9[var0])
/\ \A var0 \in DbRequestId : \A var1 \in Response : (Fluent10[var1][var0]) => (Fluent11[var1][var0])

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent8' = [Fluent8 EXCEPT![i] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT![r][i] = FALSE]
/\ Fluent6' = [Fluent6 EXCEPT![r] = TRUE]
/\ Fluent5' = [Fluent5 EXCEPT![r] = FALSE]
/\ Fluent4' = [Fluent4 EXCEPT![i][n] = FALSE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent10, Fluent3, Fluent2>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent9' = [Fluent9 EXCEPT![i] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT![i] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT![r][i] = FALSE]
/\ Fluent5' = [Fluent5 EXCEPT![r] = TRUE]
/\ Fluent10' = [Fluent10 EXCEPT![p][i] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![p] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent6, Fluent4, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent11' = [Fluent11 EXCEPT![p][i] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT![i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![i][n] = FALSE]
/\ Fluent2' = [Fluent2 EXCEPT![p] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = FALSE]
/\ UNCHANGED<<Fluent9, Fluent7, Fluent6, Fluent5, Fluent10, Fluent3, Fluent1>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
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
/\ Fluent11 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent9 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent8 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent7 = [ x0 \in Request |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent6 = [ x0 \in Request |-> FALSE]
/\ Fluent5 = [ x0 \in Request |-> FALSE]
/\ Fluent10 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent4 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> TRUE]]
/\ Fluent3 = [ x0 \in Response |-> TRUE]
/\ Fluent2 = [ x0 \in Response |-> TRUE]
/\ Fluent1 = [ x0 \in DbRequestId |-> TRUE]
/\ Fluent0 = [ x0 \in DbRequestId |-> TRUE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
