----------------------- MODULE DistributedComputation -----------------------
EXTENDS Naturals, TLC

CONSTANTS Workers

VARIABLES masterState, masterLock, masterWinner, workerState, workerTime

vars == <<masterState, masterLock, masterWinner, workerState, workerTime>>

NextUnchanged == UNCHANGED vars

Symmetry == Permutations(Workers)

CompletionTime == 5

Init ==
    /\ masterState = "init"
    /\ masterLock = {}
    /\ masterWinner = {}
    /\ workerState = [ w \in Workers |-> "idle" ]
    /\ workerTime = [ w \in Workers |-> 0 ]

DispatchWorker(w) ==
    /\ masterState = "init"
    /\ workerState' = [workerState EXCEPT![w] = "working"]
    /\ UNCHANGED<<masterState, masterLock, masterWinner, workerTime>>

MasterWait ==
    /\ masterState = "init"
    /\ workerState = [w \in Workers |-> "working"]
    /\ masterState' = "waiting"
    /\ UNCHANGED<<masterLock, masterWinner, workerState, workerTime>>

WorkerProgress(w) ==
    /\ workerState[w] = "working"
    /\ workerTime[w] < CompletionTime
    /\ workerTime' = [workerTime EXCEPT![w] = workerTime[w] + 1]
    /\ UNCHANGED<<masterState, masterLock, masterWinner, workerState>>

WorkerFinish(w) ==
    /\ workerState[w] = "working"
    /\ workerTime[w] = CompletionTime
    /\ workerState' = [workerState EXCEPT![w] = "completed"]
    /\ UNCHANGED<<masterState, masterLock, masterWinner, workerTime>>

WorkerAccessMasterLock(w) ==
    /\ workerState[w] = "completed"
    /\ masterLock = {}
    /\ workerState' = [workerState EXCEPT![w] = "lock"]
    /\ masterLock' = masterLock \cup {w}
    /\ UNCHANGED<<masterState, masterWinner, workerTime>>

WorkerNotifyMaster(w) ==
    /\ workerState[w] = "lock"
    /\ masterWinner' = masterWinner \cup {w}
    /\ UNCHANGED<<masterState, masterLock, workerState, workerTime>>

MasterComplete ==
    /\ masterState = "waiting"
    /\ masterWinner # {}
    /\ masterState' = "completed"
    /\ UNCHANGED<<masterLock, masterWinner, workerState, workerTime>>

Next ==
    \E w \in Workers :
        \/ DispatchWorker(w)
        \/ MasterWait
        \/ WorkerProgress(w)
        \/ WorkerFinish(w)
        \/ WorkerAccessMasterLock(w)
        \/ WorkerNotifyMaster(w)
        \/ MasterComplete

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ masterState \in {"init", "waiting", "completed"}
    /\ masterLock \in SUBSET Workers
    /\ masterWinner \in SUBSET Workers
    /\ workerState \in [ Workers -> {"idle", "working", "lock", "completed"} ]
    /\ workerTime \in [ Workers -> (0..CompletionTime) ]

OneWinner == \A W1,W2 \in masterWinner : W1 = W2

IndInv ==
    /\ TypeOK
    /\ OneWinner
    /\ \A WI \in Workers : \A WJ \in Workers : (masterLock = {WI}) \/ (~(masterWinner = {WI}))
    /\ \A WI \in Workers : \A WJ \in Workers : (masterLock = {WI}) \/ (~(workerState[WI] = "lock"))

IISpec == IndInv /\ [][Next]_vars

=============================================================================
\* Modification History
\* Last modified Thu Aug 08 21:05:32 EDT 2024 by idardik
\* Created Thu Aug 08 20:34:21 EDT 2024 by idardik

