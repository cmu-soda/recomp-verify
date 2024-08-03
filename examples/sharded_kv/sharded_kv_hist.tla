--------------------------- MODULE sharded_kv_hist ---------------------------


CONSTANTS Key, Value, Node

VARIABLES owner, oncePut, onceReshard, transfer_msg, table, onceRecvTransferMsg

vars == <<owner, oncePut, onceReshard, transfer_msg, table, onceRecvTransferMsg>>

CandSep ==
could not synthesize a formula! (UNSAT)

Nil == "nil"

Reshard(k,v,n_old,n_new) ==
/\ table[n_old][k] = v
/\ table' = [table EXCEPT![n_old][k] = Nil]
/\ owner' = [owner EXCEPT![n_old] = (owner[n_old] \ {k})]
/\ transfer_msg' = (transfer_msg \cup {<<n_new,k,v>>})
/\ onceReshard' = [onceReshard EXCEPT![k][v][n_old][n_new] = TRUE]
/\ UNCHANGED<<oncePut, onceRecvTransferMsg>>

RecvTransferMsg(n,k,v) ==
/\ (<<n,k,v>> \in transfer_msg)
/\ transfer_msg' = (transfer_msg \ {<<n,k,v>>})
/\ table' = [table EXCEPT![n][k] = v]
/\ owner' = [owner EXCEPT![n] = (owner[n] \cup {k})]
/\ onceRecvTransferMsg' = [onceRecvTransferMsg EXCEPT![n][k][v] = TRUE]
/\ UNCHANGED<<oncePut, onceReshard>>

Put(n,k,v) ==
/\ (k \in owner[n])
/\ table' = [table EXCEPT![n][k] = v]
/\ UNCHANGED <<owner,transfer_msg>>
/\ oncePut' = [oncePut EXCEPT![n][k][v] = TRUE]
/\ UNCHANGED<<onceReshard, onceRecvTransferMsg>>

Next ==
\/ (\E k \in Key, v \in Value, n_old,n_new \in Node : Reshard(k,v,n_old,n_new))
\/ (\E n \in Node, k \in Key, v \in Value : RecvTransferMsg(n,k,v))
\/ (\E n \in Node, k \in Key, v \in Value : Put(n,k,v))

Init ==
/\ table = [n \in Node |-> [k \in Key |-> Nil]]
/\ (owner \in [Node -> SUBSET(Key)])
/\ (\A i,j \in Node : (\A k \in Key : (((k \in owner[i]) /\ (k \in owner[j])) => i = j)))
/\ transfer_msg = {}
/\ oncePut = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Value |-> FALSE]]]
/\ onceReshard = [ x0 \in Key |-> [ x1 \in Value |-> [ x2 \in Node |-> [ x3 \in Node |-> FALSE]]]]
/\ onceRecvTransferMsg = [ x0 \in Node |-> [ x1 \in Key |-> [ x2 \in Value |-> FALSE]]]

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (table \in [Node -> [Key -> (Value \cup {Nil})]])
/\ (owner \in [Node -> SUBSET(Key)])
/\ (transfer_msg \in SUBSET((Node \X Key \X Value)))

Safety == (\A n1,n2 \in Node, k \in Key, v1,v2 \in Value : ((table[n1][k] = v1 /\ table[n2][k] = v2) => (n1 = n2 /\ v1 = v2)))
=============================================================================
