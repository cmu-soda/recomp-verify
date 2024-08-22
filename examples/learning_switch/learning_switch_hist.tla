--------------------------- MODULE learning_switch_hist ---------------------------
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Node

VARIABLES Fluent6, pending, table

vars == <<Fluent6, pending, table>>

CandSep ==
\A var0 \in Node : Fluent6[var0][var0]

NewPacket(ps,pd) ==
/\ pending' = (pending \cup {<<ps,pd,ps,ps>>})
/\ UNCHANGED table
/\ UNCHANGED<<Fluent6>>

Forward(ps,pd,sw0,sw1,nondet) ==
/\ (<<ps,pd,sw0,sw1>> \in pending)
/\ pending' = ({ <<psa,pda,sw1a,da>> \in pending : psa = nondet } \cup { <<ps,pd,sw1,d>> : d \in Node })
/\ table' = IF (ps /= sw1 /\ (\A w \in Node : (w /= sw1 => (<<ps,sw1,w>> \notin table)))) THEN (table \cup { <<px,n1,n2>> \in (Node \X Node \X Node) : (px = ps /\ ((<<ps,n1,sw1>> \in table) /\ (<<ps,sw0,n2>> \in table))) }) ELSE table
/\ Fluent6' = [Fluent6 EXCEPT![pd][ps] = FALSE]
/\ UNCHANGED<<>>

Next ==
\/ (\E ps,pd \in Node : NewPacket(ps,pd))
\/ (\E ps,pd,sw0,sw1,nondet \in Node : Forward(ps,pd,sw0,sw1,nondet))

Init ==
/\ table = { <<t,n1,n2>> \in (Node \X Node \X Node) : n1 = n2 }
/\ pending = {}
/\ Fluent6 = [ x0 \in Node |-> [ x1 \in Node |-> TRUE]]

NextUnchanged == UNCHANGED <<table,pending>>

TypeOK ==
/\ (table \in SUBSET((Node \X Node \X Node)))
/\ (pending \in SUBSET((Node \X Node \X Node \X Node)))

Safety ==
/\ (\A t,x \in Node : (<<t,x,x>> \in table))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,z>> \in table)) => (<<t,x,z>> \in table)))
/\ (\A t,x,y \in Node : (((<<t,x,y>> \in table) /\ (<<t,y,x>> \in table)) => x = y))
/\ (\A t,x,y,z \in Node : (((<<t,x,y>> \in table) /\ (<<t,x,z>> \in table)) => ((<<t,y,z>> \in table) \/ (<<t,z,y>> \in table))))
=============================================================================
