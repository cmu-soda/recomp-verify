---- MODULE toy_consensus_epr ----
\* benchmark: pyv-toy-consensus-epr

EXTENDS Naturals, FiniteSets

Node == {"n1","n2","n3","n4","n5","n6","n7","n8"}
Value == {"v1","v2","v3"}

Quorum == { S \in SUBSET Node : Cardinality(S)*2 > Cardinality(Node) }

VARIABLE voted
VARIABLE vote
VARIABLE decided

vars == <<voted,vote,decided>>

ChosenAt(Q, v) == \A n \in Q : <<n,v>> \in vote

\* Node 'i' casts a vote for value 'v'.
CastVote(n, v) == 
    /\ n \notin voted
    /\ vote' = vote \cup {<<n,v>>}
    /\ voted' = voted \cup {n}
    /\ UNCHANGED <<decided>>

\* Decide on a value 'v' with quorum 'Q'.
Decide(v, Q) == 
    /\ ChosenAt(Q, v)
    /\ decided' = decided \cup {v}
    /\ UNCHANGED <<vote,voted>>

Init ==
    /\ voted = {}
    /\ vote = {}
    /\ decided = {}

Next == 
    \/ \E i \in Node, v \in Value : CastVote(i, v)
    \/ \E v \in Value, Q \in Quorum : Decide(v, Q)

Spec == Init /\ [][Next]_vars

TypeOK == 
    /\ voted \in SUBSET Node
    /\ vote \in SUBSET (Node \X Value)
    /\ decided \in SUBSET Value

\* Can only decide on a single value
Safety == \A vi,vj \in decided : vi = vj

====
