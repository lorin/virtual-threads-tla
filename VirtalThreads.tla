---- MODULE VirtalThreads ----
EXTENDS TLC, Sequences

CONSTANTS VirtualThreads,
          CarrierThreads,
          OsWorkThreads

NULL == CHOOSE x : x \notin CarrierThreads

WorkThreads == VirtualThreads \union OsWorkThreads
PlatformThreads == CarrierThreads \union OsWorkThreads


VARIABLES lockQueue, 
          state, 
          schedule, 
          pinned, \* pinned OS threads in the pool
          inSyncBlock


TypeOk == /\ lockQueue \in Seq(WorkThreads)
          /\ state \in [WorkThreads -> {"ready", "synced", "requested", "locked", "to-desync"}]
          /\ schedule \in [WorkThreads -> PlatformThreads \union {NULL}]
          /\ pinned \subseteq CarrierThreads
          /\ inSyncBlock \subseteq VirtualThreads



IsScheduled(thread) == schedule[thread] # NULL


Init == /\ lockQueue = <<>>
           \* virutal threads are initially unscheduled, OS threads are scheduled to themselves
        /\ schedule = [t \in WorkThreads |-> IF t \in VirtualThreads THEN NULL ELSE t]
        /\ state = [t \in WorkThreads |-> "ready"]
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
       /\ UNCHANGED <<lockQueue, state, pinned, inSyncBlock>>


\* We only care about virtual threads entering synchronized blocks
EnterSynchronizedBlock(virtual) ==
    /\ state[virtual] = "ready"
    /\ IsScheduled(virtual)
    /\ pinned' = pinned \union {schedule[virtual]}
    /\ inSyncBlock' = inSyncBlock \union {virtual}
    /\ state' = [state EXCEPT ![virtual]="synced"]
    /\ UNCHANGED <<lockQueue, schedule>>

RequestLock(thread) == 
    /\ state[thread] \in {"ready", "synced"}
    /\ IsScheduled(thread)
    /\ lockQueue' = Append(lockQueue, thread)
    /\ state' = [state EXCEPT ![thread]="requested"]
    /\ UNCHANGED <<pinned, inSyncBlock, schedule>>

AcquireLock(thread) ==
    /\ state[thread] = "requested"
    /\ IsScheduled(thread)
    /\ Head(lockQueue) = thread
    /\ state' = [state EXCEPT ![thread]="locked"]
    /\ UNCHANGED <<lockQueue, pinned, inSyncBlock, schedule>>


ReleaseLock(thread) ==
    /\ state[thread] = "locked"
    /\ IsScheduled(thread)
    /\ lockQueue' = Tail(lockQueue)
    /\ state' = [state EXCEPT ![thread]=IF thread \in inSyncBlock THEN "to-desync" ELSE "ready"]
    /\ UNCHANGED <<pinned, inSyncBlock, schedule>>

ExitSynchronizedBlock(virtual) ==
    /\ state[virtual] = "to-desync"
    /\ IsScheduled(virtual)
    /\ pinned' = pinned \ {schedule[virtual]}
    /\ inSyncBlock' = inSyncBlock \ {virtual}
    /\ state' = [state EXCEPT ![virtual]="ready"]
    /\ UNCHANGED <<lockQueue, schedule>>


Next == \/ \E v \in VirtualThreads, p \in CarrierThreads : Dispatch(v, p)
        \/ \E t \in VirtualThreads : \/ EnterSynchronizedBlock(t)
                                     \/ ExitSynchronizedBlock(t)
        \/ \E t \in WorkThreads : \/ RequestLock(t)
                                  \/ AcquireLock(t)
                                  \/ ReleaseLock(t)


====