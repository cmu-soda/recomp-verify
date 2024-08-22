--------------------------- MODULE D0 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, request_sent, response_sent, Fluent10, match, response_received

vars == <<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, request_sent, response_sent, Fluent10, match, response_received>>

NextUnchanged == UNCHANGED vars
Symmetry == Permutations(Node) \cup Permutations(Request) \cup Permutations(Response) \cup Permutations(DbRequestId)

CandSep ==
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
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent10>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent11' = [Fluent11 EXCEPT![i][r] = FALSE]
/\ Fluent8' = [Fluent8 EXCEPT![n][i] = FALSE]
/\ Fluent10' = [Fluent10 EXCEPT![i][n] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent9, Fluent14, Fluent13>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent12' = [Fluent12 EXCEPT![i][r] = FALSE]
/\ Fluent14' = [Fluent14 EXCEPT![p][i] = FALSE]
/\ UNCHANGED<<Fluent11, Fluent9, Fluent8, Fluent13, Fluent10>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received>>
/\ Fluent9' = [Fluent9 EXCEPT![n][i] = FALSE]
/\ Fluent13' = [Fluent13 EXCEPT![p][i] = FALSE]
/\ UNCHANGED<<Fluent12, Fluent11, Fluent14, Fluent8, Fluent10>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent>>
/\ UNCHANGED<<Fluent12, Fluent11, Fluent9, Fluent14, Fluent8, Fluent13, Fluent10>>
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
/\ Fluent10 = [ x0 \in DbRequestId |-> [ x1 \in Node |-> TRUE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ Fluent12 \in [DbRequestId -> [Request -> BOOLEAN]]
/\ Fluent11 \in [DbRequestId -> [Request -> BOOLEAN]]
/\ Fluent9  \in [Node -> [DbRequestId -> BOOLEAN]]
/\ Fluent14 \in [Response -> [DbRequestId -> BOOLEAN]]
/\ Fluent8  \in [Node -> [DbRequestId -> BOOLEAN]]
/\ Fluent13 \in [Response -> [DbRequestId -> BOOLEAN]]
/\ Fluent10 \in [DbRequestId -> [Node -> BOOLEAN]]

RandNum == 3
TypeOKRandom ==
/\ match \in RandomSubset(7, SUBSET((Request \X Response)))
/\ request_sent \in RandomSubset(7, SUBSET((Node \X Request)))
/\ response_sent \in RandomSubset(7, SUBSET((Node \X Response)))
/\ response_received \in RandomSubset(7, SUBSET((Node \X Response)))
/\ Fluent12 \in RandomSubset(RandNum, [DbRequestId -> [Request -> BOOLEAN]])
/\ Fluent11 \in RandomSubset(RandNum, [DbRequestId -> [Request -> BOOLEAN]])
/\ Fluent9  \in RandomSubset(RandNum, [Node -> [DbRequestId -> BOOLEAN]])
/\ Fluent14 \in RandomSubset(RandNum, [Response -> [DbRequestId -> BOOLEAN]])
/\ Fluent8  \in RandomSubset(RandNum, [Node -> [DbRequestId -> BOOLEAN]])
/\ Fluent13 \in RandomSubset(RandNum, [Response -> [DbRequestId -> BOOLEAN]])
/\ Fluent10 \in RandomSubset(RandNum, [DbRequestId -> [Node -> BOOLEAN]])

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
