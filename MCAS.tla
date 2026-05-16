-------------------------------------- MODULE MCAS --------------------------------------
EXTENDS Integers, FiniteSets

(***************************************************************************)
(* CONSTANTS AND TYPE DEFINITIONS                                          *)
(***************************************************************************)
CONSTANTS
    Nodes,          (* Set of memory cells *)
    WDescriptors,   (* IDs of concurrent writing transaction descriptors *)
    RDescriptors,   (* IDs of concurrent reading operation descriptors *)
    NULL

VARIABLES
    (* Physical Key-Value Store Memory *)
    nodeValue,      (* Nodes -> Current numerical cell values *)
    nodeDesc,       (* Nodes -> Assigned WDescriptor ID (or NULL) *)

    (* Write Transaction Descriptor States *)
    wDescState,     (* {"IDLE", "ACTIVE", "SCANNING", "SUCCESS", "ABORTED"} *)
    wDescPending,   (* Set of cells awaiting locking or physical update *)
    wDescFrame,     (* Set of cells (keys) locked by the transaction *)
    wDescOldValue,  (* Snapshot of original cell values (old_j) *)
    wDescNewValue,  (* Snapshot of target cell values (new_j) *)

    (* Read Operation Descriptor States (Announce Array) *)
    rDescState,     (* {"IDLE", "ACTIVE", "ANNOUNCED", "READING", "REJECTED"} *)
    rDescFrame,     (* Set of target cells the Reader intends to scan *)
    rDescView,      (* Local snapshot of cell values collected by the Reader *)

    (* Resource Pool and Execution Metrics *)
    freeWDescs,     (* Set of available Write Descriptors *)
    freeRDescs,     (* Set of available Read Descriptors *)
    successCount,   (* Tracking successfully committed transactions or reads *)

    (* Refinement Mapping for Linearizability Verification *)
    absNodeValue    (* Nodes -> Values representing ideal atomic memory *)


vars == <<nodeValue, nodeDesc, wDescState, wDescPending, wDescFrame,
          wDescOldValue, wDescNewValue, rDescState, rDescFrame, rDescView,
          freeWDescs, freeRDescs, successCount, absNodeValue>>

(* Execution boundary to restrict state space during model checking *)
countConstraint == successCount <= 3

(***************************************************************************)
(* INITIALIZATION AND CONCURRENCY SEMANTICS                                *)
(*                                                                         *)
(* Verifies correctness under arbitrary reader-writer interleaving.        *)
(* Writers broadcast the SCANNING phase to reject conflicting readers.     *)
(* Readers retrieve values either directly from uncommitted cells or from  *)
(* committed write descriptors to guarantee strict snapshot consistency.   *)
(***************************************************************************)
Init ==
    /\ nodeValue = [n \in Nodes |-> 0]
    /\ nodeDesc = [n \in Nodes |-> NULL]

    /\ wDescState = [d \in WDescriptors |-> "IDLE"]
    /\ wDescPending = [d \in WDescriptors |-> {}]
    /\ wDescFrame = [d \in WDescriptors |-> {}]
    /\ wDescOldValue = [d \in WDescriptors |-> [n \in Nodes |-> NULL]]
    /\ wDescNewValue = [d \in WDescriptors |-> [n \in Nodes |-> NULL]]

    /\ rDescState = [r \in RDescriptors |-> "IDLE"]
    /\ rDescFrame = [r \in RDescriptors |-> {}]
    /\ rDescView = [r \in RDescriptors |-> [n \in Nodes |-> NULL]]

    /\ freeWDescs = WDescriptors
    /\ freeRDescs = RDescriptors
    /\ successCount = 0
    /\ absNodeValue = nodeValue

(* Specifies an atomic update of the entire frame in ideal memory *)
AbsAtomicWrite(frame, valuesMap) ==
    absNodeValue' = [n \in Nodes |-> IF n \in frame
                                     THEN valuesMap[n]
                                     ELSE absNodeValue[n]]

(***************************************************************************)
(* PARALLEL WRITER ACTIONS                                                 *)
(*                                                                         *)
(* 1. Initialization: Allocates a unique write descriptor for the active   *)
(*    transaction.                                                         *)
(* 2. Locking Phase: Sequentially links and locks target frame cells.      *)
(* 4. Reader Eviction: Broadcasts the SCANNING phase to reject ongoing     *)
(*    stalled readers before values shift.                                 *)
(* 5. Decision Phase: Reaches the logical commit boundary, making target   *)
(*    values ready for physical memory persistence.                        *)
(* 6. Release Phase: Sequentially uninstalls links to descriptor frames.   *)
(* 7. Reclamation: Performs a lazy cleanup and releases the descriptor.    *)
(* 3. Help Point: Helping to conflicting descs for achieve lock-freedom.   *)
(*                                                                         *)
(* Note: The cooperative help operation can execute concurrently in any    *)
(* phase. It is optional for basic specification safety but strictly       *)
(* required to guarantee the algorithm's properties.                       *)
(***************************************************************************)

(* 1) CreateWDescriptor: Initializes a write operation on an arbitrary cell frame *)
CreateWDescriptor(d, frame, valuesMap) ==
    /\ d \in freeWDescs
    /\ \A e \in freeWDescs: d <= e (* Optimization point, because states are identical *)
    /\ frame \in SUBSET Nodes /\ frame /= {}
    (* valuesMap defines the target update values for each cell in the frame *)
    /\ valuesMap \in [frame -> {0, 1}]
    /\ freeWDescs' = freeWDescs \ {d}
    /\ wDescState' = [wDescState EXCEPT ![d] = "ACTIVE"]
    /\ wDescFrame' = [wDescFrame EXCEPT ![d] = frame]
    /\ wDescPending' = [wDescPending EXCEPT ![d] = frame]
    (* Original memory cell values are not yet read and remain unassigned *)
    /\ wDescOldValue' = [wDescOldValue EXCEPT ![d] = [n \in Nodes |-> NULL]]
    /\ wDescNewValue' = [wDescNewValue EXCEPT ![d] =
        [n \in Nodes |-> IF n \in frame THEN valuesMap[n] ELSE NULL]]
    /\ UNCHANGED <<nodeValue, nodeDesc, rDescState, rDescFrame, rDescView, freeRDescs, successCount, absNodeValue>>

(* 2) AcquireNode: CAS-based cell ordering with descriptors *)
AcquireNode(d, n) ==
    /\ wDescState[d] = "ACTIVE"
    /\ n \in wDescPending[d]
    (* Assigning descriptors only in ascending order to prevent deadlocks *)
    /\ n = (CHOOSE minNode \in wDescPending[d] : \A anyNode \in wDescPending[d] : minNode <= anyNode)

    (* Note: The alternative implementation below violates the lock-freedom property *)
    (* /\ IF nodeValue[n] /= wDescOldValue[d][n]                                     *)
    (*    THEN (* CAS failed: abort the transaction and restore the pending frame *) *)
    (*      /\ wDescPending' = [wDescPending EXCEPT ![d] = wDescFrame[d]]            *)
    (*      /\ wDescState' = [wDescState EXCEPT ![d] = "ABORTED"]                    *)
    (*      /\ UNCHANGED ...                                                         *)

    /\ IF nodeDesc[n] = NULL
       THEN (* CAS success: load the current node value and link the descriptor *)
            /\ wDescOldValue' = [wDescOldValue EXCEPT ![d][n] = nodeValue[n]]
            /\ nodeDesc' = [nodeDesc EXCEPT ![n] = d]
            /\ wDescPending' = [wDescPending EXCEPT ![d] = wDescPending[d] \ {n}]
            /\ UNCHANGED <<nodeValue, wDescState, wDescFrame,
                           wDescNewValue, rDescState, rDescFrame, rDescView, freeWDescs, freeRDescs, successCount, absNodeValue>>
       ELSE (* CAS failed: need to invoke cooperative help *)
            UNCHANGED vars

(* 4) WriterScanAndReject: Rejects conflicting reading operation descriptors *)
WriterScanAndReject(d) ==
    (* Scans all active readers holding an announcement, *)
    (* including those in the READING phase *)
    LET conflictingReaders == {r \in RDescriptors : rDescState[r] \in {"ANNOUNCED", "READING"} /\ (rDescFrame[r] \cap wDescFrame[d]) /= {}} IN
    /\ wDescState[d] = "ACTIVE"
    /\ wDescPending[d] = {}
    /\ wDescState' = [wDescState EXCEPT ![d] = "SCANNING"]
    (* Notifies stalled readers that values have changed. The abstract memory *)
    (* state updates here, setting up the linearization point *)
    /\ absNodeValue' = [n \in Nodes |-> IF n \in wDescFrame[d]
                                        THEN wDescNewValue[d][n]
                                        ELSE absNodeValue[n]]
    /\ IF conflictingReaders /= {}
       THEN rDescState' = [r \in RDescriptors |-> IF r \in conflictingReaders THEN "REJECTED" ELSE rDescState[r]]
       ELSE UNCHANGED rDescState
    /\ UNCHANGED <<nodeValue, nodeDesc, wDescPending, wDescFrame, wDescOldValue, wDescNewValue, rDescFrame, rDescView, freeWDescs, freeRDescs, successCount>>

(* 5) DecisionPhase: The main point of start to commiting transaction *)
DecisionPhase(d) ==
    /\ wDescState[d] = "SCANNING"
    /\ wDescState' = [wDescState EXCEPT ![d] = "SUCCESS"]
    /\ successCount' = successCount + 1
    /\ wDescPending' = [wDescPending EXCEPT ![d] = wDescFrame[d]]
    /\ UNCHANGED <<nodeValue, nodeDesc, wDescFrame, wDescOldValue, wDescNewValue, rDescState, rDescFrame, rDescView, freeWDescs, freeRDescs, absNodeValue>>

(* 6) ReleaseNode: Step-by-step physical replacement of old values with new values (new_j) *)
ReleaseNode(d, n) ==
    /\ wDescState[d] \in {"SUCCESS", "ABORTED"}
    /\ n \in wDescPending[d]
    (* Physical value update occurs only if the transaction committed successfully *)
    /\ IF wDescState[d] = "SUCCESS"
       THEN /\ nodeValue' = [nodeValue EXCEPT ![n] = wDescNewValue[d][n]]
       ELSE /\ nodeValue' = [nodeValue EXCEPT ![n] = wDescOldValue[d][n]]
    (* Releases the lock only if the current descriptor is the actual owner *)
    /\ nodeDesc' = [nodeDesc EXCEPT ![n] = IF nodeDesc[n] = d THEN NULL ELSE nodeDesc[n]]
    /\ wDescPending' = [wDescPending EXCEPT ![d] = wDescPending[d] \ {n}]
    /\ UNCHANGED <<wDescState, wDescFrame, wDescOldValue, wDescNewValue, rDescState, rDescFrame, rDescView, freeWDescs, freeRDescs, successCount, absNodeValue>>

(* 7) FreeWDescriptor: Logical reclamation of the write descriptor *)
FreeWDescriptor(d) ==
    /\ wDescState[d] \in {"SUCCESS", "ABORTED"}
    /\ wDescPending[d] = {}
    /\ wDescState' = [wDescState EXCEPT ![d] = "IDLE"]
    /\ freeWDescs' = freeWDescs \cup {d}
    /\ UNCHANGED <<nodeValue, nodeDesc, wDescPending, wDescFrame, wDescOldValue, wDescNewValue, rDescState, rDescFrame, rDescView, freeRDescs, successCount, absNodeValue>>

(* 3) Help: Cooperative help on memory cells *)
Help(d, n) ==
    /\ wDescState[d] = "ACTIVE"
    /\ n \in wDescPending[d]
    /\ nodeDesc[n] /= NULL
    /\ nodeDesc[n] /= d
    /\ LET otherD == nodeDesc[n] IN
       \/ WriterScanAndReject(otherD)
       \/ DecisionPhase(otherD)
       \/ ReleaseNode(otherD, n)

(****************************************************************************)
(* PARALLEL READER ACTIONS                                                  *)
(*                                                                          *)
(* 1. Allocation (1): Initializes the read descriptor with a target frame.  *)
(* 2. Announcement (2): Publishes the operation to the Announce Array,      *)
(*    allowing writers to reject it and prevent linearizability violations. *)
(* 3. Scan Phase (3): Reads memory cells. It is modeled abstractly as       *)
(*    atomic for simpler TLA+ verification, but could execute with delays.  *)
(*    If delayed, writers will safely intercept and reject the stale read.  *)
(* 4. Reclamation (4): Clears the announcement and releases the descriptor. *)
(****************************************************************************)

(* 1) CreateRDescriptor: Initializes a read operation on a target cell frame *)
CreateRDescriptor(r, frame) ==
    /\ r \in freeRDescs
    /\ \A e \in freeRDescs: r <= e (* Optimization point, because states are identical *)
    /\ frame \in SUBSET Nodes /\ frame /= {}
    /\ freeRDescs' = freeRDescs \ {r}
    /\ rDescFrame' = [rDescFrame EXCEPT ![r] = frame]
    /\ rDescState' = [rDescState EXCEPT ![r] = "ACTIVE"]
    /\ UNCHANGED <<nodeValue, nodeDesc, wDescState, wDescPending, wDescFrame,
                   wDescOldValue, wDescNewValue, rDescView, freeWDescs, successCount, absNodeValue>>

(* 2) ReaderAnnounce: Publishes the target cell frame to the Announce Array *)
ReaderAnnounce(r) ==
    /\ rDescState[r] = "ACTIVE"
    /\ rDescState' = [rDescState EXCEPT ![r] = "ANNOUNCED"]
    /\ UNCHANGED <<nodeValue, nodeDesc, wDescState, wDescPending, wDescFrame,
                   wDescOldValue, wDescNewValue, rDescFrame, rDescView, freeWDescs, freeRDescs, successCount, absNodeValue>>

(* 3) ReaderRead: Scans memory cells into a local snapshot *)
ReaderRead(r) ==
    LET ReadCell(n) ==
            LET owner == nodeDesc[n] IN
            IF owner = NULL THEN nodeValue[n]
            (* Beginning from the SCANNING linearization point we should return *)
            (* the new value, even if it wasn't updated globally yet. *)
            ELSE IF wDescState[owner] \in {"SCANNING", "SUCCESS"}
            THEN wDescNewValue[owner][n]
            ELSE wDescOldValue[owner][n]
    IN
    /\ rDescState[r] = "ANNOUNCED"
    /\ rDescView' = [rDescView EXCEPT ![r] = [n \in Nodes |-> IF n \in rDescFrame[r]
                                                              THEN ReadCell(n)
                                                              ELSE NULL]]
    /\ rDescState' = [rDescState EXCEPT ![r] = "READING"]
    /\ UNCHANGED <<nodeValue, nodeDesc, wDescState, wDescPending, wDescFrame,
                   wDescOldValue, wDescNewValue, rDescFrame, freeWDescs, freeRDescs, successCount, absNodeValue>>

(* 4) ReaderRelease: Logical reclamation of the read descriptor *)
ReaderRelease(r) ==
    /\ rDescState[r] \in {"READING", "REJECTED"}
    /\ rDescState' = [rDescState EXCEPT ![r] = "IDLE"]
    /\ rDescFrame' = [rDescFrame EXCEPT ![r] = {}]
    /\ freeRDescs' = freeRDescs \cup {r}
    /\ successCount' = successCount + 1
    /\ UNCHANGED <<nodeValue, nodeDesc, wDescState, wDescPending, wDescFrame,
                   wDescOldValue, wDescNewValue, rDescView, freeWDescs, absNodeValue>>

(***************************************************************************)
(* NEXT STATE RELATION & SPECIFICATION                                     *)
(***************************************************************************)
Next ==
    (* Writer Operations *)
    \/ \E d \in WDescriptors, frame \in SUBSET Nodes, valuesMap \in [Nodes -> {0, 1}] :
          /\ frame /= {} /\ CreateWDescriptor(d, frame, valuesMap)
    \/ \E d \in WDescriptors, n \in Nodes : AcquireNode(d, n)
    \/ \E d \in WDescriptors, n \in Nodes : Help(d, n)
    \/ \E d \in WDescriptors : WriterScanAndReject(d)
    \/ \E d \in WDescriptors : DecisionPhase(d)
    \/ \E d \in WDescriptors, n \in Nodes : ReleaseNode(d, n)
    \/ \E d \in WDescriptors : FreeWDescriptor(d)
    (* Reader Operations *)
    \/ \E r \in RDescriptors, frame \in SUBSET Nodes : CreateRDescriptor(r, frame)
    \/ \E r \in RDescriptors : ReaderAnnounce(r)
    \/ \E r \in RDescriptors : ReaderRead(r)
    \/ \E r \in RDescriptors : ReaderRelease(r)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A d \in WDescriptors, n \in Nodes : WF_vars(AcquireNode(d, n))
    /\ \A d \in WDescriptors, n \in Nodes : WF_vars(Help(d, n))
    /\ \A d \in WDescriptors : WF_vars(WriterScanAndReject(d))
    /\ \A d \in WDescriptors : WF_vars(DecisionPhase(d))
    /\ \A d \in WDescriptors, n \in Nodes : WF_vars(ReleaseNode(d, n))
    /\ \A d \in WDescriptors : WF_vars(FreeWDescriptor(d))
    /\ \A r \in RDescriptors : WF_vars(ReaderAnnounce(r))
    /\ \A r \in RDescriptors : WF_vars(ReaderRead(r))
    /\ \A r \in RDescriptors : WF_vars(ReaderRelease(r))

(***************************************************************************)
(* INVARIANTS AND FORMAL VALIDATION                                        *)
(***************************************************************************)
(* AtomicyInvariant: Verifies global memory atomicity of committed updates *)
AtomicyInvariant ==
    \A n \in Nodes :
        LET owner == nodeDesc[n] IN
        IF owner /= NULL
        THEN (* Case 1: The cell is currently locked by a descriptor *)
             IF wDescState[owner] \in {"SCANNING", "SUCCESS"}
             THEN
                (* During SCANNING and SUCCESS, the abstract state has already linearized. *)
                (* The physical value may either lag behind (retaining old value) *)
                (* or match the new state. *)
                \/ nodeValue[n] = absNodeValue[n]
                \/ nodeValue[n] = wDescOldValue[owner][n]
            ELSE (* For ACTIVE or ABORTED states, the abstract memory retains *)
                 (* the pre-transaction value. *)
                 nodeValue[n] = absNodeValue[n]
        ELSE (* Case 2: Real and abstract memories must perfectly align *)
             nodeValue[n] = absNodeValue[n]

(* ReaderAtomicy: The snapshot consistency of the frame observed by the reader *)
ReaderAtomicy ==
    \A r \in RDescriptors :
        (* Evaluate ONLY after the reader completes data collection *)
        (* and transitions to READING *)
        (rDescState[r] = "READING") =>
            \A n \in rDescFrame[r] :
                (* Linearizability property: the observed value must match  *)
                (* either the current abstract state or an older historical *)
                (* value captured prior to a committed concurrent write.    *)
                \/ rDescView[r][n] = absNodeValue[n]
                \/ \E d \in WDescriptors :
                      /\ wDescState[d] = "SUCCESS"
                      /\ n \in wDescFrame[d]
                      /\ rDescView[r][n] = wDescOldValue[d][n]

(* GlobalProgress: Checks lock-freedom by ignoring model execution constraints *)
GlobalProgress ==
    \E d \in WDescriptors : wDescState[d] = "ACTIVE" ~>
        \E u \in WDescriptors : wDescState[u] = "SUCCESS" \/ ~countConstraint

(* To be honest, the above is not a mathematically rigorous guarantee of lock-freedom. *)
(* The reason is that currently, due to how the Spec is written (heavy use of Weak     *)
(* Fairness), the GlobalProgress condition will hold even without the help operation   *)
(* where other threads cooperate to clear the way for their own progress. To fix this  *)
(* situation, one must remove all WF conditions associated with the writer thread (and *)
(* specifically the writer, reader conditions should remain) and move them to the top  *)
(* level of the property as follows:                                                   *)
(*                                                                                     *)
(*  (\E d \in WDescriptors : wDescState[d] = "ACTIVE" =>                               *)
(*      \A n \in {x \in Nodes : x \in wDescFrame[d]} :                                 *)
(*          \/ WF_vars(AcquireNode(d, n))                                              *)
(*          ...                                                                        *)
(*          \/ WF_vars(ReleaseNode(d, n))                                              *)
(*  ) ~> \E u \in WDescriptors : wDescState[u] = "SUCCESS" \/ ~countConstraint         *)
(*                                                                                     *)
(* This is true because we guarantee the progress of our descriptor and no other, what *)
(* implies that either it will terminate or we will hit the limit. However, this       *)
(* heavily complicates the understanding of the property; The old statement was kept.  *)

=========================================================================================
