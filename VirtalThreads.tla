---- MODULE VirtalThreads ----
EXTENDS TLC, Naturals, Sequences

CONSTANTS PoolSize, NumVirtualThreads, NumExtraOsThreads

VARIABLES lockQueue, 
          state, 
          schedule, 
          pinned, \* pinned OS threads in the pool
          inSyncBlock

NumWorkThreads == NumVirtualThreads + NumExtraOsThreads

VirtualThreads == 1..NumVirtualThreads
PoolThreads == 1..PoolSize
WorkThreads == 1..NumWorkThreads


NULL == CHOOSE x : x \notin PoolThreads

IsScheduled(thread) == schedule[thread] # NULL


Init == /\ lockQueue = <<>>
           \* virutal threads are initially unscheduled, OS threads are scheduled to themselves
        /\ schedule = [t \in WorkThreads |-> IF t \in VirtualThreads THEN NULL ELSE t]
        /\ state = [WorkThreads |-> "ready"]
        /\ pinned = {} 
        /\ inSyncBlock = {}
        

\* Dispatch a virtual thread to a carrier thread, bumping the other thread
\* We can only do this when the carrier is not pinned, and when the virtual threads is not already pinned
\* We need to unschedule the previous thread
Dispatch(virtual, carrier) ==
    LET prev == CHOOSE t \in VirtualThreads : schedule[t] = carrier
    IN /\ carrier \notin pinned
       /\ \/ schedule[virtual] = NULL 
          \/ schedule[virtual] \notin pinned
       /\ schedule' = IF \E t \in VirtualThreads : schedule[t] = carrier 
                      THEN [schedule EXCEPT ![virtual]=carrier, ![prev]=NULL]
                      ELSE [schedule EXCEPT ![virtual]=carrier]
       /\ UNCHANGED <<lockQueue, state, pinned>>


\* We only care about virtual threads entering synchronized blocks
EnterSynchronizedBlock(virtual) ==
    /\ state[virtual] = "ready"
    /\ IsScheduled(virtual)
    /\ pinned' = pinned \union {schedule[virtual]}
    /\ inSyncBlock' = inSyncBlock \union {virtual}
    /\ state' = [state EXCEPT ![virtual]="synced"]

RequestLock(thread) == 
    /\ state[thread] \in {"ready", "synced"}
    /\ IsScheduled(thread)
    /\ lockQueue' = Append(lockQueue, thread)
    /\ state' = [state EXCEPT ![thread]="requested"]
    /\ UNCHANGED pinned

AcquireLock(thread) ==
    /\ state[thread] = "requested"
    /\ IsScheduled(thread)
    /\ Head(lockQueue) = thread
    /\ state' = [state EXCEPT ![thread]="locked"]
    /\ UNCHANGED <<lockQueue, pinned>>


ReleaseLock(thread) ==
    /\ state[thread] = "locked"
    /\ IsScheduled(thread)
    /\ lockQueue' = Tail(lockQueue)
    /\ state' = [state EXCEPT ![thread]=IF thread \in inSyncBlock THEN "to-desync" ELSE "ready"]
    /\ UNCHANGED <<pinned>>

ExitSynchronizedBlock(virtual) ==
    /\ state[virtual] = "to-desync"
    /\ IsScheduled(virtual)
    /\ pinned' = pinned \ {schedule[virtual]}
    /\ inSyncBlock' = inSyncBlock \ {virtual}
    /\ state' = [state EXCEPT ![virtual]="ready"]
    /\ UNCHANGED <<lockQueue>>


Next == \/ \E v \in VirtualThreads, p \in PoolThreads : Dispatch(v, p)
        \/ \E t \in VirtualThreads : \/ EnterSynchronizedBlock(t)
                                     \/ ExitSynchronizedBlock(t)
        \/ \E t \in WorkThreads : \/ RequestLock(t)
                                  \/ AcquireLock(t)
                                  \/ ReleaseLock(t)


====