--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, request_sent, Fluent6, response_sent, Fluent5, Fluent10, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0

vars == <<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, request_sent, Fluent6, response_sent, Fluent5, Fluent10, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in DbRequestId : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in Node : (Fluent2[var0]) => (Fluent3[var0])
/\ \A var0 \in Response : (Fluent5[var0]) => (Fluent4[var0])
/\ \A var0 \in Request : (Fluent6[var0]) => (Fluent7[var0])
/\ \A var0 \in DbRequestId : \E var1 \in Node : Fluent8[var1][var0]
/\ \A var0 \in DbRequestId : \A var1 \in Node : (Fluent10[var0][var1]) => (Fluent9[var1][var0])
/\ \A var0 \in Request : \A var1 \in DbRequestId : (Fluent11[var1][var0]) => (Fluent12[var1][var0])
/\ \A var0 \in Response : \A var1 \in DbRequestId : (Fluent14[var0][var1]) => (Fluent13[var0][var1])

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent11' = [Fluent11 EXCEPT![i][r] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT![n][i] = FALSE]
/\ Fluent6' = [Fluent6 EXCEPT![r] = FALSE]
/\ Fluent10' = [Fluent10 EXCEPT![i][n] = FALSE]
/\ Fluent3' = [Fluent3 EXCEPT![n] = TRUE]
/\ UNCHANGED<<Fluent12, Fluent9, Fluent14, Fluent13, Fluent7, Fluent5, Fluent4, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent12' = [Fluent12 EXCEPT![i][r] = FALSE]
/\ Fluent14' = [Fluent14 EXCEPT![p][i] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT![r] = FALSE]
/\ Fluent4' = [Fluent4 EXCEPT![p] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![i] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent13, Fluent6, Fluent5, Fluent10, Fluent3, Fluent2, Fluent0>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent9' = [Fluent9 EXCEPT![n][i] = FALSE]
/\ Fluent13' = [Fluent13 EXCEPT![p][i] = FALSE]
/\ Fluent5' = [Fluent5 EXCEPT![p] = TRUE]
/\ Fluent2' = [Fluent2 EXCEPT![n] = TRUE]
/\ Fluent0' = [Fluent0 EXCEPT![i] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent14, Fluent8, Fluent7, Fluent6, Fluent10, Fluent4, Fluent3, Fluent1>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
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
/\ Fluent12 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> TRUE]]
/\ Fluent11 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> TRUE]]
/\ Fluent9 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent14 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent8 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent13 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent7 = [ x0 \in Request |-> TRUE]
/\ Fluent6 = [ x0 \in Request |-> TRUE]
/\ Fluent5 = [ x0 \in Response |-> FALSE]
/\ Fluent10 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> TRUE]]
/\ Fluent4 = [ x0 \in Response |-> FALSE]
/\ Fluent3 = [ x0 \in Node |-> FALSE]
/\ Fluent2 = [ x0 \in Node |-> FALSE]
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
