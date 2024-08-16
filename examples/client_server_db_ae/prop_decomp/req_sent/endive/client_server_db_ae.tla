--------------------------- MODULE client_server_db_ae ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC, Randomization

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, t, request_sent, response_sent, match, response_received, Fluent1, Fluent0, db_response_sent

vars == <<db_request_sent, t, request_sent, response_sent, match, response_received, Fluent1, Fluent0, db_response_sent>>

CandSep ==
\A var0 \in Node : (Fluent1[var0]) => (Fluent0[var0])

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received,db_request_sent,db_response_sent,t>>
/\ UNCHANGED<<Fluent1, Fluent0>>

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<match,request_sent,response_sent,response_received,db_response_sent>>
/\ Fluent0' = [Fluent0 EXCEPT![n] = TRUE]
/\ UNCHANGED<<Fluent1>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ (<<r,p>> \in match)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<match,request_sent,response_sent,response_received,db_request_sent,t>>
/\ UNCHANGED<<Fluent1, Fluent0>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received,db_request_sent,db_response_sent,t>>
/\ UNCHANGED<<Fluent1, Fluent0>>

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent,db_request_sent,db_response_sent,t>>
/\ Fluent1' = [Fluent1 EXCEPT![n] = TRUE]
/\ UNCHANGED<<Fluent0>>

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
/\ db_request_sent = {}
/\ db_response_sent = {}
/\ t = {}
/\ Fluent1 = [ x0 \in Node |-> FALSE]
/\ Fluent0 = [ x0 \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))
/\ Fluent1 \in [Node -> BOOLEAN]
/\ Fluent0 \in [Node -> BOOLEAN]

TypeOKRandom ==
/\ match \in RandomSubset(5, SUBSET((Request \X Response)))
/\ request_sent \in RandomSubset(5, SUBSET((Node \X Request)))
/\ response_sent \in RandomSubset(5, SUBSET((Node \X Response)))
/\ response_received \in RandomSubset(5, SUBSET((Node \X Response)))
/\ db_request_sent \in RandomSubset(5, SUBSET((DbRequestId \X Request)))
/\ db_response_sent \in RandomSubset(5, SUBSET((DbRequestId \X Response)))
/\ t \in RandomSubset(5, SUBSET((DbRequestId \X Node)))
/\ Fluent1 \in RandomSubset(5, [Node -> BOOLEAN])
/\ Fluent0 \in RandomSubset(5, [Node -> BOOLEAN])

Safety == (\A n \in Node, p \in Response : (\E r \in Request : ((<<n,p>> \in response_received) => (<<n,r>> \in request_sent))))
D0_I1 == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : \E VARR2 \in Request : (<<VARI,VARR2>> \in request_sent) \/ (~(Fluent0[VARI]))

D1_Safety == \A var0 \in Node : (Fluent1[var0]) => (Fluent0[var0])
D1_I1 == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : (Fluent0[VARI]) \/ (~(<<VARI,VARP>> \in response_sent))
D1_I2 == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : (Fluent0[VARI]) \/ (~(<<VARID,VARI>> \in t))

IndInv ==
    /\ TypeOK

    \* D0
    /\ Safety
    /\ D0_I1

    \* D1
    /\ D1_Safety
    /\ D1_I1
    /\ D1_I2

IISpec == TypeOKRandom /\ IndInv /\ [][Next]_vars

(*
Compare our compositional II to the monolithic one; ours has fewer conjuncts and only refers to vars from the 1st two components, which
is more precise than the monolithic one (which references db_ vars, which are irrelevant to upholding the safety property).

Inv273_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(<<VARI,VARP>> \in response_sent))
Inv209_1_1_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : (<<VARJ,VARP>> \in response_sent) \/ (~(<<VARJ,VARP>> \in response_received))
Inv388_1_2_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : ~(<<VARID,VARR>> \in db_request_sent) \/ (~(NoneWithId(VARID)))
Inv2873_2_3_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ (~(<<VARID,VARI>> \in t)) \/ (~(<<VARID,VARP>> \in db_response_sent))
Inv380_1_0_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : ~(<<VARID,VARP>> \in db_response_sent) \/ (~(NoneWithId(VARID)))
Inv923_2_1_def == \A VARI \in Node : \A VARID \in DbRequestId : \A VARR \in Request : \A VARJ \in Node : \A VARP \in Response : (<<VARI,VARR>> \in request_sent) \/ (~(<<VARID,VARR>> \in db_request_sent)) \/ (~(<<VARID,VARI>> \in t))

\* The inductive invariant candidate.
IndAuto ==
  /\ ReqSentSafety
  /\ Inv273_1_0_def
  /\ Inv209_1_1_def
  /\ Inv388_1_2_def
  /\ Inv2873_2_3_def
  /\ Inv380_1_0_def
  /\ Inv923_2_1_def
----------------------------------------
Initial random seed: 20
opt_quant_minimize: 0
Total number of CTIs eliminated: 2513
Total number of invariants generated: 458
Total number of invariants checked: 6412
CTI generation duration: 483.418445 secs.
Invariant checking duration: 82.494752 secs.
CTI elimination checks duration: 13.008320 secs.
Total duration: 579.00 secs.
python3 endive.py --spec benchmarks/client_server_db_ae --seed 20 --ninvs   3  2368.32s user 19.14s system 412% cpu 9:39.09 total
*)

=============================================================================
