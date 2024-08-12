----------------------- MODULE Master -----------------------
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS Workers, Result

VARIABLES masterState, masterLock, masterResult, masterNumWorkersDone 

vars == <<masterState, masterLock, masterResult, masterNumWorkersDone>>

NextUnchanged == UNCHANGED vars

Symmetry == Permutations(Workers)

Init ==
    /\ masterState = "dispatching"
    /\ masterLock = {}
    /\ masterResult = {}
    /\ masterNumWorkersDone = 0

DispatchWorker(w) ==
    /\ masterState = "dispatching"
    /\ UNCHANGED<<masterState, masterLock, masterResult, masterNumWorkersDone>>

DoneDispatching ==
    /\ masterState = "dispatching"
    /\ masterState' = "doneDispatching"
    /\ UNCHANGED<<masterLock, masterResult, masterNumWorkersDone>>

MasterLock ==
    /\ masterState = "doneDispatching"
    /\ masterLock = {}
    /\ masterState' = "locked"
    /\ masterLock' = masterLock \cup {"master"}
    /\ UNCHANGED<<masterResult, masterNumWorkersDone>>

\* when the master calls await() it releases the lock
AwaitWorker ==
    /\ masterState = "locked"
    /\ masterResult = {}
    /\ masterNumWorkersDone < Cardinality(Workers)
    /\ masterState' = "waiting"
    /\ masterLock' = masterLock \ {"master"}
    /\ UNCHANGED<<masterResult, masterNumWorkersDone>>

WorkerFinished(w, r) ==
    /\ masterLock = {}
    /\ masterLock' = masterLock \cup {w}
    \* non-deterministically, we may choose to reject the result and
    \* wait for the next worker to finish
    /\ \/ masterResult' = masterResult \cup {r}
       \/ masterResult' = masterResult
    /\ UNCHANGED<<masterState, masterNumWorkersDone>>

\* signaling the master will cause w to release the lock and
\* the master to gain the lock
SignalMaster(w) ==
    /\ masterState = "waiting"
    /\ w \in masterLock
    /\ masterState' = "locked"
    /\ masterLock' = (masterLock \ {w}) \cup {"master"}
    /\ masterNumWorkersDone' = masterNumWorkersDone + 1
    /\ UNCHANGED<<masterResult>>

MasterFinished ==
    /\ masterState = "locked"
    /\ \/ masterResult # {}
       \/ masterNumWorkersDone = Cardinality(Workers)
    /\ masterState' = "finished"
    /\ masterLock' = masterLock \ {"master"}
    /\ UNCHANGED<<masterResult, masterNumWorkersDone>>

KillWorker(w) ==
    /\ masterState = "finished"
    /\ UNCHANGED<<masterState, masterLock, masterResult, masterNumWorkersDone>>

Next ==
    \E w \in Workers :
    \E r \in Result :
        \/ DispatchWorker(w)
        \/ DoneDispatching
        \/ MasterLock
        \/ AwaitWorker
        \/ WorkerFinished(w, r)
        \/ SignalMaster(w)
        \/ MasterFinished
        \/ KillWorker(w)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ masterState \in {"dispatching", "doneDispatching", "locked", "waiting", "finished"}
    /\ masterLock \in SUBSET (Workers \cup {"master"})
    /\ masterResult \in SUBSET Result
    /\ masterNumWorkersDone \in Nat

\*OneResult == \A w1,w2 \in masterResult : w1 = w2

MasterLockMutex ==
    \A p,q \in (Workers \cup {"master"}) : (p \in masterLock /\ q \in masterLock) => (p = q)

=============================================================================
