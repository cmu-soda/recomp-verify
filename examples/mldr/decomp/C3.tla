--------------------------- MODULE C3 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

VARIABLES configVersion

CONSTANT Server

Secondary == "secondary"
Primary == "primary"
Nil == "nil"
InitTerm == 1
FinNat == 0..5

vars == <<configVersion>>

Quorums(S) == { i \in SUBSET(S) : (Cardinality(i) * 2) > Cardinality(S) }

QuorumsAt(i) == Quorums

Empty(s) == Len(s) = 0

NewerConfig(ci,cj) ==
\/ ci[2] > cj[2]
\/ (ci[2] = cj[2] /\ ci[1] > cj[1])

NewerOrEqualConfig(ci,cj) == (NewerConfig(ci,cj) \/ ci = cj)

QuorumsOverlap(x,y) == (\A qx \in Quorums(x), qy \in Quorums(y) : (qx \cap qy) /= {})

ConfigIsCommitted(s,term,Q) ==
/\ (\A t \in Q : configVersion[s] = configVersion[t])

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ UNCHANGED <<configVersion>>

Reconfig(i,newConfig,term,Q) ==
/\ ConfigIsCommitted(i,term,Q)
/\ (i \in newConfig)
/\ configVersion' = [configVersion EXCEPT![i] = (configVersion[i] + 1)]

SendConfig(i,j) ==
/\ configVersion' = [configVersion EXCEPT![j] = configVersion[i]]

Init ==
/\ configVersion = [i \in Server |-> 1]

Next ==
\/ (\E s \in Server, newConfig \in SUBSET(Server) : (\E term \in FinNat : (\E Q \in SUBSET(Server) : Reconfig(s,newConfig,term,Q))))
\/ (\E s,t \in Server : SendConfig(s,t))

Spec == (Init /\ [][Next]_vars)

CV(i) == <<configVersion[i]>>

TypeOK ==
/\ (configVersion \in [Server -> Nat])
=============================================================================
