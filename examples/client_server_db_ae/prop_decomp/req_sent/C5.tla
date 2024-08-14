--------------------------- MODULE C5 ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node, Request, Response, DbRequestId

VARIABLES match

vars == <<match>>

DbProcessRequest(i,r,p) ==
/\ (<<r,p>> \in match)
/\ UNCHANGED <<match>>

Next ==
\/ (\E r \in Request, i \in DbRequestId, p \in Response : DbProcessRequest(i,r,p))

Init ==
/\ (match \in SUBSET((Request \X Response)))

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (match \in SUBSET((Request \X Response)))
=============================================================================
