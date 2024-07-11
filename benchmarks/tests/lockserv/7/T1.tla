--------------------------- MODULE T1 ---------------------------


VARIABLES server_holds_lock, grant_msg, unlock_msg, lock_msg

Node == {"n1","n2","n3","n4","n5","n6","n7"}

vars == <<lock_msg,grant_msg,unlock_msg,server_holds_lock>>

SendLock(n) ==
/\ lock_msg' = [lock_msg EXCEPT![n] = TRUE]
/\ UNCHANGED <<unlock_msg,grant_msg,server_holds_lock>>

RecvLock(n) ==
/\ server_holds_lock
/\ lock_msg[n]
/\ server_holds_lock' = FALSE
/\ lock_msg' = [k \in Node |-> (lock_msg[k] /\ k /= n)]
/\ grant_msg' = [grant_msg EXCEPT![n] = TRUE]
/\ UNCHANGED <<unlock_msg>>

RecvGrant(n) ==
/\ grant_msg[n]
/\ grant_msg' = [k \in Node |-> (grant_msg[k] /\ k /= n)]
/\ UNCHANGED <<lock_msg,unlock_msg,server_holds_lock>>

Unlock(n) ==
/\ unlock_msg' = [unlock_msg EXCEPT![n] = TRUE]
/\ UNCHANGED <<lock_msg,grant_msg,server_holds_lock>>

RecvUnlock(n) ==
/\ unlock_msg[n]
/\ unlock_msg' = [k \in Node |-> (unlock_msg[k] /\ k /= n)]
/\ server_holds_lock' = TRUE
/\ UNCHANGED <<lock_msg,grant_msg>>

Next ==
\/ (\E n \in Node : SendLock(n))
\/ (\E n \in Node : RecvLock(n))
\/ (\E n \in Node : RecvGrant(n))
\/ (\E n \in Node : Unlock(n))
\/ (\E n \in Node : RecvUnlock(n))

Init ==
/\ lock_msg = [n \in Node |-> FALSE]
/\ unlock_msg = [n \in Node |-> FALSE]
/\ grant_msg = [n \in Node |-> FALSE]
/\ server_holds_lock = TRUE

Spec == (Init /\ [][Next]_vars)

TypeOK ==
/\ (lock_msg \in [Node -> BOOLEAN])
/\ (grant_msg \in [Node -> BOOLEAN])
/\ (unlock_msg \in [Node -> BOOLEAN])
/\ (server_holds_lock \in BOOLEAN)
=============================================================================
