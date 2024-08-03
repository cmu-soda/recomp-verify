--------------------------- MODULE D0 ---------------------------
EXTENDS TLC, Randomization

CONSTANTS Node, Request, Response

VARIABLES onceRespond, request_sent, match, onceNewRequest, response_received, onceReceiveResponse

vars == <<onceRespond, request_sent, match, onceNewRequest, response_received, onceReceiveResponse>>

ResponseMatched(n,p) ==
\E r \in Request :
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)

NewRequest(n,r) ==
/\ request_sent' = (request_sent \cup {<<n,r>>})
/\ UNCHANGED <<response_received,match>>
/\ onceNewRequest' = [onceNewRequest EXCEPT![n][r] = TRUE]
/\ UNCHANGED<<onceRespond, onceReceiveResponse>>

Respond(n,r,p) ==
/\ (<<n,r>> \in request_sent)
/\ (<<r,p>> \in match)
/\ UNCHANGED <<request_sent,response_received,match>>
/\ onceRespond' = [onceRespond EXCEPT![n][r][p] = TRUE]
/\ UNCHANGED<<onceNewRequest, onceReceiveResponse>>

ReceiveResponse(n,p) ==
/\ response_received' = (response_received \cup {<<n,p>>})
/\ UNCHANGED <<request_sent,match>>
/\ onceReceiveResponse' = [onceReceiveResponse EXCEPT![n][p] = TRUE]
/\ UNCHANGED<<onceRespond, onceNewRequest>>

OrigNext ==
\/ (\E n \in Node, r \in Request : NewRequest(n,r))
\/ (\E n \in Node, r \in Request, p \in Response : Respond(n,r,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))
/\ request_sent = {}
/\ response_received = {}
/\ onceRespond = [ x0 \in Node |-> [ x1 \in Request |-> [ x2 \in Response |-> FALSE]]]
/\ onceNewRequest = [ x0 \in Node |-> [ x1 \in Request |-> FALSE]]
/\ onceReceiveResponse = [ x0 \in Node |-> [ x1 \in Response |-> FALSE]]

Assumption == \A var0 \in Response : \A var1 \in Node : (onceReceiveResponse[var1][var0]) => (\E var2 \in Request : onceRespond[var1][var2][var0])

Next == OrigNext /\ Assumption /\ Assumption'

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
/\ (request_sent \in SUBSET((Node \X Request)))
/\ (response_received \in SUBSET((Node \X Response)))
/\ onceRespond \in [Node -> [Request -> [Response -> BOOLEAN]]]
/\ onceNewRequest \in [Node -> [Request -> BOOLEAN]]
/\ onceReceiveResponse \in [Node -> [Response -> BOOLEAN]]

RandNum == 20

TypeOKRandom ==
/\ (match \in SUBSET(Request \X Response))
/\ (request_sent \in SUBSET(Node \X Request))
/\ (response_received \in SUBSET(Node \X Response))
/\ onceRespond \in RandomSubset(RandNum, [Node -> [Request -> [Response -> BOOLEAN]]])
/\ onceNewRequest \in RandomSubset(RandNum, [Node -> [Request -> BOOLEAN]])
/\ onceReceiveResponse \in RandomSubset(RandNum, [Node -> [Response -> BOOLEAN]])

NextUnchanged == UNCHANGED vars

Safety == (\A n \in Node, p \in Response : ((<<n,p>> \in response_received) => ResponseMatched(n,p)))

IndInv ==
    /\ TypeOK
    /\ \A VARI \in Node : \A VARJ \in Node : \A VARR \in Request : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ ((VARI=VARJ /\ match = match))
    /\ Safety

IndInvRand ==
    /\ TypeOKRandom
    /\ \A VARI \in Node : \A VARJ \in Node : \A VARR \in Request : \A VARP \in Response : (ResponseMatched(VARI,VARP)) \/ ((VARI=VARJ /\ match = match))
    /\ Safety

IISpec == (IndInv /\ [][Next]_vars)
=============================================================================
