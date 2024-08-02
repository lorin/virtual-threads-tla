---- MODULE VirtualThreads ----
EXTENDS Sequences

CONSTANTS VirtualThreads,
          CarrierThreads,
          FreePlatformThreads


PlatformThreads == CarrierThreads \union FreePlatformThreads
WorkThreads == VirtualThreads \union FreePlatformThreads

VARIABLES pc,
          schedule,
          inSyncBlock,
          pinned,
          lockQueue

NULL == CHOOSE x : x \notin PlatformThreads

TypeOk == /\ pc \in [WorkThreads -> {"ready", "to-enter-sync", "requested", "locked", "in-critical-section", "to-exit-sync", "done"}]
          /\ schedule \in [WorkThreads -> PlatformThreads \union {NULL}]
          /\ inSyncBlock \subseteq VirtualThreads
          /\ pinned \subseteq CarrierThreads
          /\ lockQueue \in Seq(WorkThreads)


IsScheduled(thread) == schedule[thread] # NULL


Init == /\ lockQueue = <<>>
           \* virutal threads are initially unscheduled, OS threads are scheduled to themselves
        /\ schedule = [t \in WorkThreads |-> IF t \in VirtualThreads THEN NULL ELSE t]
        /\ pc = [t \in WorkThreads |-> "ready"]
        /\ pinned = {}
        /\ inSyncBlock = {}

\* A thread has the lock if it's in one of the pc that requires the lock
HasTheLock(thread) == pc[thread] \in {"locked", "in-critical-section"}

\* Mount a virtual thread to a carrier thread, bumping the other thread
\* We can only do this when the carrier is not pinned, and when the virtual threads is not already pinned
\* We need to unschedule the previous thread
Mount(virtual, carrier) ==
    LET carrierInUse == \E t \in VirtualThreads : schedule[t] = carrier
         prev == CHOOSE t \in VirtualThreads : schedule[t] = carrier
    IN /\ carrier \notin pinned
       /\ \/ schedule[virtual] = NULL
          \/ schedule[virtual] \notin pinned
       \* If a virtual thread has the lock already, then don't pre-empt it.
       /\ carrierInUse => ~HasTheLock(prev)
       /\ schedule' = IF carrierInUse
                      THEN [schedule EXCEPT ![virtual]=carrier, ![prev]=NULL]
                      ELSE [schedule EXCEPT ![virtual]=carrier]
       /\ UNCHANGED <<lockQueue, pc, pinned, inSyncBlock>>


\* When this fires, virtual thread enters a synchronized block
ChooseToEnterSynchronizedBlock(virtual) ==
    /\ pc[virtual] = "ready"
    /\ IsScheduled(virtual)
    /\ virtual \notin inSyncBlock
    /\ pc' = [pc EXCEPT ![virtual]="to-enter-sync"]
    /\ UNCHANGED <<lockQueue, schedule, pinned, inSyncBlock>>


\* We only care about virtual threads entering synchronized blocks
EnterSynchronizedBlock(virtual) ==
    /\ pc[virtual] = "to-enter-sync"
    /\ IsScheduled(virtual)
    /\ pinned' = pinned \union {schedule[virtual]}
    /\ inSyncBlock' = inSyncBlock \union {virtual}
    /\ pc' = [pc EXCEPT ![virtual]="ready"]
    /\ UNCHANGED <<lockQueue, schedule>>


\* Atomically request and acquire the lock
\* This can only fire when thread holds the lock
RequestAndAcquireLock(thread) ==
    /\ pc[thread] = "ready"
    /\ IsScheduled(thread)
    /\ lockQueue = <<>>
    /\ lockQueue' = Append(lockQueue, thread)
    /\ pc' = [pc EXCEPT ![thread]="locked"]
    /\ UNCHANGED <<pinned, inSyncBlock, schedule>>

RequestLock(thread) ==
    /\ pc[thread] = "ready"
    /\ IsScheduled(thread)
    /\ lockQueue # <<>>
    /\ lockQueue' = Append(lockQueue, thread)
    /\ pc' = [pc EXCEPT ![thread]="requested"]
    /\ UNCHANGED <<pinned, inSyncBlock, schedule>>

AcquireLock(thread) ==
    /\ pc[thread] = "requested"
    /\ IsScheduled(thread)
    /\ Head(lockQueue) = thread
    /\ pc' = [pc EXCEPT ![thread]="locked"]
    /\ UNCHANGED <<lockQueue, pinned, inSyncBlock, schedule>>


CriticalSection(thread) ==
    /\ pc[thread] = "locked"
    /\ IsScheduled(thread)
    /\ pc' = [pc EXCEPT ![thread]="in-critical-section"]
    /\ UNCHANGED <<lockQueue, pinned, inSyncBlock, schedule>>

ReleaseLock(thread) ==
    /\ pc[thread] = "in-critical-section"
    /\ IsScheduled(thread)
    /\ lockQueue' = Tail(lockQueue)
    /\ pc' = [pc EXCEPT ![thread]=IF thread \in inSyncBlock THEN "to-exit-sync" ELSE "done"]
    /\ UNCHANGED <<pinned, inSyncBlock, schedule>>

ExitSynchronizedBlock(virtual) ==
    /\ pc[virtual] = "to-exit-sync"
    /\ IsScheduled(virtual)
    /\ pinned' = pinned \ {schedule[virtual]}
    /\ inSyncBlock' = inSyncBlock \ {virtual}
    /\ pc' = [pc EXCEPT ![virtual]="done"]
    /\ UNCHANGED <<lockQueue, schedule>>


Next == \/ \E t \in VirtualThreads : \/ ChooseToEnterSynchronizedBlock(t)
                                     \/ EnterSynchronizedBlock(t)
                                     \/ ExitSynchronizedBlock(t)
                                     \/ \E p \in CarrierThreads : Mount(t, p)
        \/ \E t \in WorkThreads : \/ RequestLock(t)
                                  \/ AcquireLock(t)
                                  \/ RequestAndAcquireLock(t)
                                  \/ CriticalSection(t)
                                  \/ ReleaseLock(t)

PlatformThreadsAreSelfScheduled ==
    \A t \in FreePlatformThreads : schedule[t] = t

VirtualThreadsCantShareCarriers ==
    \A v1,v2 \in VirtualThreads : \/ schedule[v1] = NULL
                                  \/ schedule[v2] = NULL
                                  \/ (schedule[v1] = schedule[v2]) => v1=v2

HeadHasTheLock ==
    \A t \in WorkThreads : HasTheLock(t) => t = Head(lockQueue)

MutualExclusion ==
    \A t1, t2 \in WorkThreads : (pc[t1]="in-critical-section" /\ pc[t2]="in-critical-section") => t1=t2

====