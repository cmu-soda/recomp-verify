--------------------------- MODULE C1 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

VARIABLES currentTerm, state

CONSTANT Server

Secondary == "secondary"
Primary == "primary"
Nil == "nil"
InitTerm == 1
FinNat == 0..10

vars == <<currentTerm,state>>

Quorums(S) == { i \in SUBSET(S) : (Cardinality(i) * 2) > Cardinality(S) }

Empty(s) == Len(s) = 0

NewerConfig(ci,cj) ==
\/ ci[2] > cj[2]
\/ (ci[2] = cj[2] /\ ci[1] > cj[1])

NewerOrEqualConfig(ci,cj) == (NewerConfig(ci,cj) \/ ci = cj)

CanVoteForConfig(i,j,term) ==
/\ currentTerm[i] < term

QuorumsOverlap(x,y) == (\A qx \in Quorums(x), qy \in Quorums(y) : (qx \cap qy) /= {})

ConfigIsCommitted(s,term,Q) ==
/\ state[s] = Primary
/\ currentTerm[s] = term
/\ (\A t \in Q : currentTerm[t] = currentTerm[s])

UpdateTermsExpr(i,j) ==
/\ currentTerm[i] > currentTerm[j]
/\ currentTerm' = [currentTerm EXCEPT![j] = currentTerm[i]]
/\ state' = [state EXCEPT![j] = Secondary]

UpdateTerms(i,j) ==
/\ UpdateTermsExpr(i,j)

BecomeLeader(i,voteQuorum,newTerm) ==
/\ newTerm = (currentTerm[i] + 1)
/\ (i \in voteQuorum)
/\ (\A v \in voteQuorum : CanVoteForConfig(v,i,newTerm))
/\ currentTerm' = [s \in Server |-> IF (s \in voteQuorum) THEN newTerm ELSE currentTerm[s]]
/\ state' = [s \in Server |-> IF s = i THEN Primary ELSE IF (s \in voteQuorum) THEN Secondary ELSE state[s]]

Reconfig(i,newConfig,term,Q) ==
/\ state[i] = Primary
/\ ConfigIsCommitted(i,term,Q)
/\ (i \in newConfig)
/\ UNCHANGED <<currentTerm,state>>

SendConfig(i,j) ==
/\ state[j] = Secondary
/\ UNCHANGED <<currentTerm,state>>

Init ==
/\ currentTerm = [i \in Server |-> InitTerm]
/\ state = [i \in Server |-> Secondary]

Next ==
\/ (\E s \in Server, newConfig \in SUBSET(Server) : (\E term \in FinNat : (\E Q \in SUBSET(Server) : Reconfig(s,newConfig,term,Q))))
\/ (\E s,t \in Server : SendConfig(s,t))
\/ (\E s,t \in Server : UpdateTerms(s,t))

Spec == (Init /\ [][Next]_vars)

CV(i) == <<>>

OnePrimaryPerTerm == (\A s,t \in Server : ((state[s] = Primary /\ state[t] = Primary /\ currentTerm[s] = currentTerm[t]) => s = t))

TypeOK ==
/\ (currentTerm \in [Server -> Nat])
/\ (state \in [Server -> {Secondary,Primary}])
=============================================================================
