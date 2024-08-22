--------------------------- MODULE client_server_db_ae_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES db_request_sent, Fluent14, Fluent13, t, request_sent, response_sent, match, response_received, db_response_sent

vars == <<db_request_sent, Fluent14, Fluent13, t, request_sent, response_sent, match, response_received, db_response_sent>>

CandSep ==
\A var0 \in Response : \A var1 \in DbRequestId : (Fluent14[var0][var1]) => (Fluent13[var0][var1])

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_sent,response_received,db_request_sent,db_response_sent,t>>
/\ UNCHANGED<<Fluent14, Fluent13>>

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ db_request_sent' = (db_request_sent \cup {<<i,r>>})
/\ UNCHANGED <<match,request_sent,response_sent,response_received,db_response_sent>>
/\ UNCHANGED<<Fluent14, Fluent13>>

DbProcessRequest(i,r,p) ==
/\ (<<i,r>> \in db_request_sent)
/\ (<<r,p>> \in match)
/\ db_response_sent' = (db_response_sent \cup {<<i,p>>})
/\ UNCHANGED <<match,request_sent,response_sent,response_received,db_request_sent,t>>
/\ Fluent14' = [Fluent14 EXCEPT![p][i] = FALSE]
/\ UNCHANGED<<Fluent13>>

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,p>> \in db_response_sent)
/\ (<<i,n>> \in t)
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_received,db_request_sent,db_response_sent,t>>
/\ Fluent13' = [Fluent13 EXCEPT![p][i] = FALSE]
/\ UNCHANGED<<Fluent14>>

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent,response_sent,db_request_sent,db_response_sent,t>>
/\ UNCHANGED<<Fluent14, Fluent13>>

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
/\ Fluent14 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> TRUE]]
/\ Fluent13 = [ x0 \in Response |-> [ x1 \in DbRequestId |-> TRUE]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ (db_request_sent \in SUBSET((DbRequestId \X Request)))
/\ (db_response_sent \in SUBSET((DbRequestId \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
