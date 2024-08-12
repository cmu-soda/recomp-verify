----------------------- MODULE Workers -----------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Workers, Result

VARIABLES workerState, workerLock

vars == <<workerState, workerLock>>

NextUnchanged == UNCHANGED vars

Symmetry == Permutations(Workers)

Init ==
    /\ workerState = [w \in Workers |-> "idle"]
    /\ workerLock = {}

DispatchWorker(w) ==
    /\ workerState[w] = "idle"
    /\ workerState' = [workerState EXCEPT![w] = "working"]
    /\ UNCHANGED<<workerLock>>

DoneDispatching ==
    /\ workerState = [w \in Workers |-> "working"]
    /\ UNCHANGED<<workerState, workerLock>>

DoWork(w) ==
    /\ workerState[w] = "idle"
    /\ workerState' = [workerState EXCEPT![w] = "working"]
    /\ UNCHANGED<<workerLock>>

WorkerFinished(w, r) ==
    /\ workerState[w] = "working"
    /\ workerState' = [workerState EXCEPT![w] = "finished"]
    /\ UNCHANGED<<workerLock>>

\* signaling the master will cause w to release the lock and
\* the master to gain the lock
SignalMaster(w) ==
    /\ workerState[w] = "finished"
    /\ workerState' = [workerState EXCEPT![w] = "signaled"]
    /\ UNCHANGED<<workerLock>>

KillWorker(w) ==
    /\ workerState[w] = "signaled"
    /\ workerState' = [workerState EXCEPT![w] = "killed"]
    /\ UNCHANGED<<workerLock>>

Next ==
    \E w \in Workers :
    \E r \in Result :
        \/ DispatchWorker(w)
        \/ DoneDispatching
        \/ DoWork(w)
        \/ WorkerFinished(w, r)
        \/ SignalMaster(w)
        \/ KillWorker(w)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ workerState \in [Workers -> {"idle", "working", "finished", "signaled", "killed"}]
    /\ workerLock \in SUBSET Workers

=============================================================================
