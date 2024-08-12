--------------------------- MODULE D0_ii ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES Fluent8, Fluent7, request_sent, response_sent, Fluent4, match, response_received, t

vars == <<Fluent8, Fluent7, request_sent, response_sent, Fluent4, match, response_received, t>>

Assumption ==
/\ \A var0 \in DbRequestId : \E var1 \in Request : Fluent4[var0][var1]
/\ \A var0 \in DbRequestId : \A var1 \in Response : (Fluent7[var1][var0]) => (Fluent8[var1][var0])

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received,t>>
/\ UNCHANGED<<Fluent8, Fluent7, Fluent4>>

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_sent,response_received>>
/\ Fluent4' = [Fluent4 EXCEPT![i][r] = FALSE]
/\ UNCHANGED<<Fluent8, Fluent7>>

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_sent,response_received,t>>
/\ Fluent8' = [Fluent8 EXCEPT![p][i] = TRUE]
/\ Fluent4' = [Fluent4 EXCEPT![i][r] = FALSE]
/\ UNCHANGED<<Fluent7>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,n>> \in t)
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received,t>>
/\ Fluent7' = [Fluent7 EXCEPT![p][i] = TRUE]
/\ UNCHANGED<<Fluent8, Fluent4>>

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent,t>>
/\ UNCHANGED<<Fluent8, Fluent7, Fluent4>>

OrigNext ==
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
/\ Fluent8 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent7 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> FALSE]]
/\ Fluent4 = [ x0 \in DbRequestId |-> [ x1 \in Request |-> TRUE]]

Next == OrigNext /\ Assumption /\ Assumption'
Spec == (Init /\ [][Next]_vars)

NextUnchanged == UNCHANGED vars

Symmetry == Permutations(Node) \cup Permutations(Request) \cup Permutations(Response) \cup Permutations(DbRequestId)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
/\ Fluent8 \in [Response -> [DbRequestId -> BOOLEAN]]
/\ Fluent7 \in [Response -> [DbRequestId -> BOOLEAN]]
/\ Fluent4 \in [DbRequestId -> [Request -> BOOLEAN]]

RandNum == 5

TypeOKRandom ==
/\ match \in RandomSubset(20, SUBSET (Request \X Response))
/\ request_sent \in RandomSubset(10, SUBSET (Node \X Request))
/\ response_sent \in RandomSubset(10, SUBSET (Node \X Response))
/\ response_received \in RandomSubset(10, SUBSET (Node \X Response))
/\ t \in RandomSetOfSubsets(10, 3, (DbRequestId \X Node))
/\ Fluent8 \in RandomSubset(RandNum, [Response -> [DbRequestId -> BOOLEAN]])
/\ Fluent7 \in RandomSubset(RandNum, [Response -> [DbRequestId -> BOOLEAN]])
/\ Fluent4 \in RandomSubset(RandNum, [DbRequestId -> [Request -> BOOLEAN]])

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))

\* python3 endive.py --spec benchmarks/D0 --seed 26 --ninvs 15000 --niters 10 --nrounds 10 --num_simulate_traces 50000 --simulate_depth 6 --tlc_workers 6
IndInv ==
    /\ TypeOK
    /\ Safety
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (ResponseMatched(VARI,VARP)) \/ (~(<<VARI,VARP>> \in response_sent))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (NoneWithId(VARID)) \/ (~(Fluent4[VARID][VARR2]))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARJ,VARP>> \in response_sent) \/ (~(<<VARJ,VARP>> \in response_received))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARR2,VARP>> \in match) \/ (~(Fluent8[VARP][VARID]))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARJ,VARR2>> \in request_sent) \/ (~(<<VARID,VARJ>> \in t))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : ~(Fluent7[VARP][VARID]) \/ (~(NoneWithId(VARID)))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : ~(Fluent4[VARID][VARR2]) \/ (~(Fluent8[VARP][VARID]))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (ResponseMatched(VARI,VARP)) \/ (~(<<VARID,VARI>> \in t) \/ (~(Fluent8[VARP][VARID])))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARI,VARR>> \in request_sent) \/ ((Fluent4[VARID][VARR]) \/ (~(<<VARID,VARI>> \in t)))
    /\ \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARR,VARP>> \in match) \/ ((Fluent4[VARID][VARR]) \/ (~(Fluent8[VARP][VARID])))

IISpec == TypeOKRandom /\ IndInv /\ [][Next]_vars

=============================================================================
