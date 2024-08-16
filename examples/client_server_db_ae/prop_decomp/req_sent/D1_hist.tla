--------------------------- MODULE D1_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES t, response_sent, Fluent1, Fluent0

vars == <<t, response_sent, Fluent1, Fluent0>>

CandSep ==
TRUE

NoneWithId(i) == (\A n \in Node : (<<i,n>> \notin t))

ServerProcessRequest(n,r,i) ==
/\ NoneWithId(i)
/\ t' = (t \cup {<<i,n>>})
/\ UNCHANGED <<response_sent>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent0' = [Fluent0 EXCEPT![n] = TRUE]
/\ UNCHANGED<<Fluent1>>
/\ CandSep'

ServerProcessDbResponse(n,i,p) ==
/\ (<<i,n>> \in t)
/\ response_sent' = (response_sent \cup {<<n,p>>})
/\ UNCHANGED <<t>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ UNCHANGED<<Fluent1, Fluent0>>
/\ CandSep'

ReceiveResponse(n,p) ==
/\ (<<n,p>> \in response_sent)
/\ UNCHANGED <<response_sent,t>>
/\ UNCHANGED<<>>
/\ CandSep'
/\ Fluent1' = [Fluent1 EXCEPT![n] = TRUE]
/\ UNCHANGED<<Fluent0>>
/\ CandSep'

Next ==
\/ (\E n \in Node, r \in Request, i \in DbRequestId : ServerProcessRequest(n,r,i))
\/ (\E n \in Node, i \in DbRequestId, p \in Response : ServerProcessDbResponse(n,i,p))
\/ (\E n \in Node, p \in Response : ReceiveResponse(n,p))

Init ==
/\ response_sent = {}
/\ t = {}
/\ Fluent1 = [ x0 \in Node |-> FALSE]
/\ Fluent0 = [ x0 \in Node |-> FALSE]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (response_sent \in SUBSET((Node \X Response)))
/\ (t \in SUBSET((DbRequestId \X Node)))

Safety ==
/\ \A var0 \in Node : (Fluent1[var0]) => (Fluent0[var0])
=============================================================================
