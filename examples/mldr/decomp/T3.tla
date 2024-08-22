--------------------------- MODULE T3 ---------------------------
EXTENDS Naturals, Integers, Sequences, FiniteSets

VARIABLES config

CONSTANT Server

Secondary == "secondary"
Primary == "primary"
Nil == "nil"
InitTerm == 1
FinNat == 0..5

vars == <<config>>

Quorums(S) == { i \in SUBSET(S) : (Cardinality(i) * 2) > Cardinality(S) }

QuorumsAt(i) == Quorums(config[i])

Empty(s) == Len(s) = 0

NewerConfig(ci,cj) ==
\/ ci[2] > cj[2]
\/ (ci[2] = cj[2] /\ ci[1] > cj[1])

NewerOrEqualConfig(ci,cj) == (NewerConfig(ci,cj) \/ ci = cj)

QuorumsOverlap(x,y) == (\A qx \in Quorums(x), qy \in Quorums(y) : (qx \cap qy) /= {})

ConfigIsCommitted(s,term,Q) ==
/\ (Q \in Quorums(config[s]))

BecomeLeader(i,voteQuorum,newTerm) ==
/\ (i \in config[i])
/\ (i \in voteQuorum)
/\ UNCHANGED <<config>>

Reconfig(i,newConfig,term,Q) ==
/\ ConfigIsCommitted(i,term,Q)
/\ QuorumsOverlap(config[i],newConfig)
/\ (i \in newConfig)
/\ config' = [config EXCEPT![i] = newConfig]

SendConfig(i,j) ==
/\ config' = [config EXCEPT![j] = config[i]]

Init ==
/\ (\E initConfig \in SUBSET(Server) : (initConfig /= {} /\ config = [i \in Server |-> initConfig]))

Next ==
\/ (\E s \in Server, newConfig \in SUBSET(Server) : (\E term \in FinNat : (\E Q \in SUBSET(Server) : Reconfig(s,newConfig,term,Q))))
\/ (\E s,t \in Server : SendConfig(s,t))
\/ (\E i \in Server : (\E Q \in Quorums(config[i]) : (\E newTerm \in FinNat : BecomeLeader(i,Q,newTerm))))

Spec == (Init /\ [][Next]_vars)

CV(i) == <<>>

ConfigDisabled(i) == (\A Q \in Quorums(config[i]) : (\E n \in Q : NewerConfig(CV(n),CV(i))))

TypeOK ==
/\ (config \in [Server -> SUBSET(Server)])
=============================================================================
