--------------------------- MODULE C2 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

VARIABLES configTerm

CONSTANT Server

Secondary == "secondary"
Primary == "primary"
Nil == "nil"
InitTerm == 1
FinNat == 0..5

vars == <<configTerm>>

Quorums(S) == { i \in SUBSET(S) : (Cardinality(i) * 2) > Cardinality(S) }

QuorumsAt(i) == Quorums

Empty(s) == Len(s) = 0

IsNewerConfig(i,j) ==
\/ configTerm[i] > configTerm[j]

IsNewerOrEqualConfig(i,j) ==
\/ IsNewerConfig(i,j)

NewerConfig(ci,cj) ==
\/ ci[2] > cj[2]
\/ (ci[2] = cj[2] /\ ci[1] > cj[1])

NewerOrEqualConfig(ci,cj) == (NewerConfig(ci,cj) \/ ci = cj)

CanVoteForConfig(i,j,term) ==
/\ IsNewerOrEqualConfig(j,i)

QuorumsOverlap(x,y) == (\A qx \in Quorums(x), qy \in Quorums(y) : (qx \cap qy) /= {})

ConfigIsCommitted(s,term,Q) ==
/\ configTerm[s] = term
/\ (\A t \in Q : configTerm[s] = configTerm[t])

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForConfig(v,i,newTerm))
/\ configTerm' = [configTerm EXCEPT![i] = newTerm]

Reconfig(i,newConfig,term,Q) ==
/\ ConfigIsCommitted(i,term,Q)
/\ (i \in newConfig)
/\ configTerm' = [configTerm EXCEPT![i] = term]

SendConfig(i,j) ==
/\ IsNewerConfig(i,j)
/\ configTerm' = [configTerm EXCEPT![j] = configTerm[i]]

Init ==
/\ configTerm = [i \in Server |-> InitTerm]

Next ==
\/ (\E s \in Server, newConfig \in SUBSET(Server) : (\E term \in FinNat : (\E Q \in SUBSET(Server) : Reconfig(s,newConfig,term,Q))))
\/ (\E s,t \in Server : SendConfig(s,t))

Spec == (Init /\ [][Next]_vars)

CV(i) == <<configTerm[i]>>

TypeOK ==
/\ (configTerm \in [Server -> Nat])
=============================================================================
