--------------------------- MODULE D0_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES request_sent, match, onceNewRequest, response_received, onceDbProcessRequest, onceReceiveResponse, onceServerProcessRequest

vars == <<request_sent, match, onceNewRequest, response_received, onceDbProcessRequest, onceReceiveResponse, onceServerProcessRequest>>

CandSep ==
/\ 

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<match,response_received>>
/\ onceNewRequest' = [onceNewRequest EXCEPT![n][r] = TRUE]
/\ UNCHANGED<<onceDbProcessRequest, onceReceiveResponse, onceServerProcessRequest>>
/\ CandSep'

ServerProcessRequest(n,r,i) ==
/\ (<<n,r>> \in request_sent)
/\ UNCHANGED <<match,request_sent,response_received>>
/\ onceServerProcessRequest' = [onceServerProcessRequest EXCEPT![n][r][i] = TRUE]
/\ UNCHANGED<<onceNewRequest, onceDbProcessRequest, onceReceiveResponse>>
/\ CandSep'

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match,request_sent,response_received>>
/\ onceDbProcessRequest' = [onceDbProcessRequest EXCEPT![i][r][p] = TRUE]
/\ UNCHANGED<<onceNewRequest, onceReceiveResponse, onceServerProcessRequest>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<match,request_sent>>
/\ onceReceiveResponse' = [onceReceiveResponse EXCEPT![n][p] = TRUE]
/\ UNCHANGED<<onceNewRequest, onceDbProcessRequest, onceServerProcessRequest>>
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
/\ onceNewRequest = [ x0 \in Node |-> [ x1 \in Request |-> FALSE]]
/\ onceDbProcessRequest = [ x0 \in DbRequestId |-> [ x1 \in Request |-> [ x2 \in Response |-> FALSE]]]
/\ onceReceiveResponse = [ x0 \in Node |-> [ x1 \in Response |-> FALSE]]
/\ onceServerProcessRequest = [ x0 \in Node |-> [ x1 \in Request |-> [ x2 \in DbRequestId |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_received \in SUBSET((Node \X Response)))

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))
=============================================================================
