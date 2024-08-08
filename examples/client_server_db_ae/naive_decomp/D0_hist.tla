--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent12, Fluent11, Fluent9, Fluent8, Fluent7, request_sent, Fluent6, Fluent5, Fluent10, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0

vars == <<Fluent12, Fluent11, Fluent9, Fluent8, Fluent7, request_sent, Fluent6, Fluent5, Fluent10, Fluent4, match, Fluent3, response_received, Fluent2, Fluent1, Fluent0>>

CandSep ==
/\ \A var0 \in Response : (Fluent1[var0]) => (Fluent0[var0])
/\ \A var0 \in Request : (Fluent3[var0]) => (Fluent2[var0])
/\ \A var0 \in DbRequestId : (Fluent5[var0]) => (Fluent4[var0])
/\ \A var0 \in Node : (Fluent6[var0]) => (Fluent7[var0])
/\ \A var0 \in DbRequestId : \E var1 \in Node : Fluent8[var1][var0]
/\ \A var0 \in Node : (\A var1 \in DbRequestId : (Fluent11[var0][var1]) => (Fluent9[var1])) => (Fluent10[var0])
/\ \A var0 \in DbRequestId : \A var1 \in Response : \E var2 \in Request : Fluent12[var0][var2]

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_received>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent8, Fluent7, Fluent6, Fluent5, Fluent10, Fluent4, Fluent3, Fluent2, Fluent1, Fluent0>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent12' = [Fluent12 EXCEPT![i][r] = FALSE]
/\ Fluent11' = [Fluent11 EXCEPT![n][i] = TRUE]
/\ Fluent9' = [Fluent9 EXCEPT![i] = TRUE]
/\ Fluent8' = [Fluent8 EXCEPT![n][i] = FALSE]
/\ Fluent7' = [Fluent7 EXCEPT![n] = TRUE]
/\ Fluent6' = [Fluent6 EXCEPT![n] = FALSE]
/\ Fluent5' = [Fluent5 EXCEPT![i] = FALSE]
/\ Fluent4' = [Fluent4 EXCEPT![i] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT![r] = FALSE]
/\ Fluent2' = [Fluent2 EXCEPT![r] = TRUE]
/\ UNCHANGED<<Fluent10, Fluent1, Fluent0>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent12' = [Fluent12 EXCEPT![i][r] = FALSE]
/\ Fluent9' = [Fluent9 EXCEPT![i] = FALSE]
/\ Fluent5' = [Fluent5 EXCEPT![i] = TRUE]
/\ Fluent3' = [Fluent3 EXCEPT![r] = TRUE]
/\ Fluent1' = [Fluent1 EXCEPT![p] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent8, Fluent7, Fluent6, Fluent10, Fluent4, Fluent2, Fluent0>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent>>
/\ Fluent7' = [Fluent7 EXCEPT![n] = FALSE]
/\ Fluent10' = [Fluent10 EXCEPT![n] = FALSE]
/\ Fluent0' = [Fluent0 EXCEPT![p] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent8, Fluent6, Fluent5, Fluent4, Fluent3, Fluent2, Fluent1>>
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
/\ Fluent12 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> TRUE]]
/\ Fluent11 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent9 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent8 = [ x0 \in Node |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent7 = [ x0 \in Node |-> TRUE]
/\ Fluent6 = [ x0 \in Node |-> TRUE]
/\ Fluent5 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent10 = [ x0 \in Node |-> TRUE]
/\ Fluent4 = [ x0 \in DbRequestId |-> FALSE]
/\ Fluent3 = [ x0 \in Request |-> FALSE]
/\ Fluent2 = [ x0 \in Request |-> FALSE]
/\ Fluent1 = [ x0 \in Response |-> TRUE]
/\ Fluent0 = [ x0 \in Response |-> TRUE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
