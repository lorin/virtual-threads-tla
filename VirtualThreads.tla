---- MODULE VirtualThreads ----
EXTENDS TLC, Sequences

CONSTANTS VirtualThreads,
          CarrierThreads,
          FreePlatformThreads

NULL == CHOOSE x : x \notin CarrierThreads

PlatformThreads == CarrierThreads \union FreePlatformThreads
WorkThreads == VirtualThreads \union FreePlatformThreads


VARIABLES lockQueue, 
          state, 
          schedule, 
          pinned, \* pinned OS threads in the pool
          inSyncBlock


TypeOk == /\ lockQueue \in Seq(WorkThreads)
          /\ state \in [WorkThreads -> {"ready", "to-enter-sync", "requested", "locked", "cs", "to-exit-sync"}]
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
        

\* Mount a virtual thread to a carrier thread, bumping the other thread
\* We can only do this when the carrier is not pinned, and when the virtual threads is not already pinned
\* We need to unschedule the previous thread
Mount(virtual, carrier) ==
    LET prev == CHOOSE t \in VirtualThreads : schedule[t] = carrier
    IN /\ carrier \notin pinned
       /\ \/ schedule[virtual] = NULL 
          \/ schedule[virtual] \notin pinned
       /\ schedule' = IF \E t \in VirtualThreads : schedule[t] = carrier 
                      THEN [schedule EXCEPT ![virtual]=carrier, ![prev]=NULL]
                      ELSE [schedule EXCEPT ![virtual]=carrier]
       /\ UNCHANGED <<lockQueue, state, pinned, inSyncBlock>>


\* When this fires, virtual thread enters a synchronized block
ChooseToEnterSynchronizedBlock(virtual) ==
    /\ state[virtual] = "ready"
    /\ IsScheduled(virtual)
    /\ virtual \notin inSyncBlock
    /\ state' = [state EXCEPT ![virtual]="to-enter-sync"]
    /\ UNCHANGED <<lockQueue, schedule, pinned, inSyncBlock>>


\* We only care about virtual threads entering synchronized blocks
EnterSynchronizedBlock(virtual) ==
    /\ state[virtual] = "to-enter-sync"
    /\ IsScheduled(virtual)
    /\ pinned' = pinned \union {schedule[virtual]}
    /\ inSyncBlock' = inSyncBlock \union {virtual}
    /\ state' = [state EXCEPT ![virtual]="ready"]
    /\ UNCHANGED <<lockQueue, schedule>>


\* Atomically request and acquire the lock
\* This can only fire when thread holds the lock
RequestAndAcquireLock(thread) == 
    /\ state[thread] = "ready"
    /\ IsScheduled(thread)
    /\ lockQueue = <<>>
    /\ lockQueue' = Append(lockQueue, thread)
    /\ state' = [state EXCEPT ![thread]="locked"]
    /\ UNCHANGED <<pinned, inSyncBlock, schedule>>

RequestLock(thread) == 
    /\ state[thread] = "ready"
    /\ IsScheduled(thread)
    /\ lockQueue # <<>>
    /\ lockQueue' = Append(lockQueue, thread)
    /\ state' = [state EXCEPT ![thread]="requested"]
    /\ UNCHANGED <<pinned, inSyncBlock, schedule>>

AcquireLock(thread) ==
    /\ state[thread] = "requested"
    /\ IsScheduled(thread)
    /\ Head(lockQueue) = thread
    /\ state' = [state EXCEPT ![thread]="locked"]
    /\ UNCHANGED <<lockQueue, pinned, inSyncBlock, schedule>>


CriticalSection(thread) ==
    /\ state[thread] = "locked"
    /\ IsScheduled(thread)
    /\ state' = [state EXCEPT ![thread]="cs"]
    /\ UNCHANGED <<lockQueue, pinned, inSyncBlock, schedule>>

ReleaseLock(thread) ==
    /\ state[thread] = "cs"
    /\ IsScheduled(thread)
    /\ lockQueue' = Tail(lockQueue)
    /\ state' = [state EXCEPT ![thread]=IF thread \in inSyncBlock THEN "to-exit-sync" ELSE "ready"]
    /\ UNCHANGED <<pinned, inSyncBlock, schedule>>

ExitSynchronizedBlock(virtual) ==
    /\ state[virtual] = "to-exit-sync"
    /\ IsScheduled(virtual)
    /\ pinned' = pinned \ {schedule[virtual]}
    /\ inSyncBlock' = inSyncBlock \ {virtual}
    /\ state' = [state EXCEPT ![virtual]="ready"]
    /\ UNCHANGED <<lockQueue, schedule>>


Next == \/ \E v \in VirtualThreads, p \in CarrierThreads : Mount(v, p)
        \/ \E t \in VirtualThreads : 
                                     \/ ChooseToEnterSynchronizedBlock(t)
                                     \/ EnterSynchronizedBlock(t)
                                     \/ ExitSynchronizedBlock(t)
        \/ \E t \in WorkThreads : \/ RequestLock(t)
                                  \/ AcquireLock(t)
                                  \/ RequestAndAcquireLock(t)
                                  \/ CriticalSection(t)
                                  \/ ReleaseLock(t)


MutualExclusion ==
    \A t1, t2 \in WorkThreads : (state[t1]="cs" /\ state[t2]="cs") => t1=t2

====