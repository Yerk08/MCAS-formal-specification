------------------------------------ MODULE TreeCAS ------------------------------------
EXTENDS Integers, FiniteSets

(**************************************************************************************)
(* CONSTANTS AND TYPES: We will represent the tree as a set of nodes, which connected *)
(* to the structs. Structs are the other node's type, which consider on the structure *)
(* of children data. There are links loop: node -> struct -> node -> ...              *)
(**************************************************************************************)
CONSTANTS
    Nodes,        (* The set of all nodes, which does not change in this spec *)
    Descriptors,  (* The set of all available descriptors *)
    NULL

(**************************************************************************************)
(* STATE VARIABLES: We should consider states of nodes, structs and descriptors       *)
(**************************************************************************************)
VARIABLES
    nodeStruct,          (* Maps each Node to its current Struct *)
    nodeDesc,            (* Reference to a descriptor in a cell, or NULL *)
    structLinks,         (* Maps each Struct to a set of target Nodes *)
    descState,           (* "IDLE", "ACTIVE", "COMMITTING", "SUCCESS", "ABORTED" *)
    descPending,         (* Unacquired nodes for each descriptor *)
    descFrame,           (* Node frame assigned to a descriptor *)
    descExpectedStruct,  (* Snapshot of node's struct when descriptor was made *)
    descNewStruct,       (* Pre-allocated new structs to write into nodes *)
    freeDescs,           (* Pool of available descriptors *)
    freeStruct           (* Number of the last free structure to use *)

FreeStructConstraint == freeStruct <= 6

vars == <<nodeStruct, nodeDesc, structLinks, descState, descPending, 
          descFrame, descExpectedStruct, descNewStruct, freeDescs, freeStruct>>

(*************************************)
(* DYNAMIC GRAPH GEOMETRY            *)
(*************************************)
(* Checks if the struct of the parent node points to the child node *)
IsEdge(parent, child) == child \in structLinks[nodeStruct[parent]]

ReachableFrom(src) ==
    (* Find all unvisited direct children of the current node *)
    LET RECURSIVE Step(_)
        Step(current) == 
            LET next == current \cup { child \in Nodes :
                \E parent \in current : IsEdge(parent, child) } IN
            IF next = current
            THEN (* If no new children are found *)
                current
            ELSE Step(next)
    IN Step({src})

(* Validates if a set of nodes forms a valid connected frame in the current graph *)
IsValidFrame(f) ==
    /\ f /= {}
    /\ f \in SUBSET Nodes
    (* At least one "operation root" r must exist within the frame *)
    /\ \E r \in f :
        (* For any other node n within this frame *)
        /\ \A n \in f :
            (* n must be reachable from r exclusively through the nodes of this same frame *)
            n = r \/ n \in ReachableFrom(r)

(***************************************************************************)
(* INITIALIZATION                                                          *)
(* Our goal is to verify node reachability when concurrent threads can     *)
(* delete a target node, potentially causing us to lose connection to      *)
(* the root. Therefore, it is sufficient to model the tree structure       *)
(* as a static pair of nodes: 0 -> 1.                                      *)
(***************************************************************************)
Init == 
    (* Construct a small tree where 0 is the root and 1 is the child *)
    /\ nodeStruct = [n \in Nodes |-> n]
    (* Initialize structLinks as a finite lazy array *)
    /\ LET InitialTree == [s \in {0, 1} |-> IF s = 0 THEN {1} ELSE {}]
           Domain == DOMAIN InitialTree
       IN
       /\ freeStruct = (CHOOSE x \in Domain : \A y \in Domain : x >= y) + 1
       /\ structLinks = [s \in 0..(freeStruct - 1) |-> 
                            IF s \in Domain THEN InitialTree[s] ELSE {}]
    (* Initially all descriptors are empty *)
    /\ nodeDesc = [n \in Nodes |-> NULL]
    /\ descState = [d \in Descriptors |-> "IDLE"]
    /\ descPending = [d \in Descriptors |-> {}]
    /\ descFrame = [d \in Descriptors |-> {}]
    /\ descExpectedStruct = [d \in Descriptors |-> [n \in Nodes |-> NULL]]
    /\ descNewStruct = [d \in Descriptors |-> [n \in Nodes |-> NULL]]
    (* We will allocate the required ones if we want to start an operation *)
    /\ freeDescs = Descriptors

(*************************)
(* HELPER ACTIONS        *)
(*************************)
ExecuteAcquire(d, n) ==
    (* We will need an operator that marks nodes with our descriptor *)
    /\ nodeDesc' = [nodeDesc EXCEPT ![n] = d]
    /\ descPending' = [descPending EXCEPT ![d] = descPending[d] \ {n}]
    /\ UNCHANGED <<nodeStruct, structLinks, descState, descFrame, 
                   descExpectedStruct, descNewStruct, freeDescs, freeStruct>>

StartCommit(d) ==
    (* We will also need an operation that saves states after a successful *)
    (* frame replacement, performing value updates using other flush operations. *)
    /\ descState[d] = "ACTIVE"
    /\ descPending[d] = {}
    /\ descState' = [descState EXCEPT ![d] = "COMMITTING"]
    /\ descPending' = [descPending EXCEPT ![d] = descFrame[d]]
    /\ UNCHANGED <<nodeStruct, nodeDesc, structLinks, descFrame, 
                   descExpectedStruct, descNewStruct, freeDescs, freeStruct>>

(***************************************)
(* MAIN EVENTS (SYSTEM STEPS)          *)
(***************************************)

(* 1) Create descriptor, pre-allocating new structs by excessively copying old ones *)
CreateDescriptor(d, frame, linksMap) ==
    (* We need as many fresh structures as there are nodes in the frame *)
    LET count == Cardinality(frame)
        (* The block of sequential struct indices allocated for this frame *)
        allocatedIndices == freeStruct..(freeStruct + count - 1)
    IN
    /\ d \in freeDescs
    /\ IsValidFrame(frame)
    /\ \A n \in frame : linksMap[n] = structLinks[nodeStruct[n]]
    (* Ensure all allocated indices fall within the valid Nat set *)
    /\ allocatedIndices \subseteq Nat
    /\ \E structMap \in [frame -> allocatedIndices] :
        (* Ensure the mapping from nodes to fresh structures is a bijection *)
        /\ \A s \in allocatedIndices : \E n \in frame : structMap[n] = s
        /\ freeDescs' = freeDescs \ {d}
        (* Advance the global index counter past the allocated block *)
        /\ freeStruct' = freeStruct + count
        /\ descState' = [descState EXCEPT ![d] = "ACTIVE"]
        /\ descFrame' = [descFrame EXCEPT ![d] = frame]
        /\ descPending' = [descPending EXCEPT ![d] = frame]
        (* Take a snapshot of the current node structures *)
        (* to detect concurrent modifications later       *)
        /\ descExpectedStruct' = [descExpectedStruct EXCEPT ![d] =
            [n \in Nodes |-> IF n \in frame THEN nodeStruct[n] ELSE NULL]]
        (* Map the pre-allocated fresh structs to the *)
        (* corresponding nodes within the frame *)
        /\ descNewStruct' = [descNewStruct EXCEPT ![d] =
            [n \in Nodes |-> IF n \in frame THEN structMap[n] ELSE NULL]]
        (* Initialize the links inside the newly allocated *)
        (* structs using the number of occupied links *)
        /\ structLinks' = [s \in 0..(freeStruct + count - 1) |->
            IF s \in allocatedIndices 
            THEN linksMap[CHOOSE n \in frame : structMap[n] = s] 
            ELSE structLinks[s]]
        /\ UNCHANGED <<nodeStruct, nodeDesc>>

(* 2) Attempt node acquisition via CAS with validation checks *)
AcquireNode(d, n) ==
    (* Ensure the descriptor is currently active and the target node still needs to be acquired *)
    /\ descState[d] = "ACTIVE" 
    /\ n \in descPending[d]
    (* Nodes must be acquired in ascending order to prevent deadlocks *)
    /\ n = (CHOOSE minNode \in descPending[d] : \A anyNode \in descPending[d] : minNode <= anyNode)    
    (* Any parent node within the operation frame must be acquired first *)
    /\ \A parent \in Nodes :
        (IsEdge(parent, n) /\
         nodeDesc[parent] /= NULL /\
         nodeDesc[parent] /= d) => FALSE
    (* Main part of acquiring nodes *)
    /\ IF nodeStruct[n] /= descExpectedStruct[d][n]
       THEN (* The underlying node structure has changed since the descriptor creation. *)
            (* Abort the transaction to preserve consistency. *)
            /\ descState' = [descState EXCEPT ![d] = "ABORTED"]
            /\ UNCHANGED <<nodeStruct, nodeDesc, structLinks, descPending, 
                           descFrame, descExpectedStruct, descNewStruct, freeDescs, freeStruct>>
       ELSE IF nodeDesc[n] = NULL 
       THEN (* CAS SUCCESS: Lock the node *)
            ExecuteAcquire(d, n)
       ELSE (* CAS FAIL: Node is occupied *)
            UNCHANGED vars

(* 4) Step-by-step redirection of node pointers to redundant copied structs *)
CommitStep(d) ==
    (* Only execute if the descriptor is currently active or already in the middle of a commit phase *)
    /\ descState[d] \in {"ACTIVE", "COMMITTING"}
    /\ IF descState[d] = "ACTIVE" /\ descPending[d] = {}
       THEN (* All target nodes are successfully locked via CAS. *)
            StartCommit(d)
       ELSE IF descState[d] = "COMMITTING" /\ descPending[d] /= {}
       THEN \E n \in descPending[d] :
                /\ nodeStruct' = [nodeStruct EXCEPT ![n] = descNewStruct[d][n]]
                /\ descPending' = [descPending EXCEPT ![d] = descPending[d] \ {n}]
                /\ UNCHANGED <<nodeDesc, descState, structLinks, descFrame, descExpectedStruct, descNewStruct, freeDescs, freeStruct>>
       ELSE IF descState[d] = "COMMITTING" /\ descPending[d] = {}
       THEN 
            (* All node redirects are complete and visible to the graph. *)
            /\ descState' = [descState EXCEPT ![d] = "SUCCESS"]
            /\ UNCHANGED <<nodeStruct, nodeDesc, structLinks, descPending, descFrame, descExpectedStruct, descNewStruct, freeDescs, freeStruct>>
       ELSE UNCHANGED vars

(* 5) Release locked nodes and return descriptor to the free pool *)
ReleaseDescriptor(d) ==
    /\ descState[d] \in {"SUCCESS", "ABORTED"} 
    /\ d \notin freeDescs
    /\ nodeDesc' = [n \in Nodes |-> IF nodeDesc[n] = d THEN NULL ELSE nodeDesc[n]]
    /\ descState' = [descState EXCEPT ![d] = "IDLE"]
    /\ freeDescs' = freeDescs \cup {d}
    (* freeStruct monotonically increases during CreateDescriptor *)
    /\ UNCHANGED <<nodeStruct, structLinks, descPending, descFrame, 
                   descExpectedStruct, descNewStruct, freeStruct>>

(* 3) Help operation: Cooperatively advance or clean up another descriptor if it blocks our path *)
Help(d, n) ==
    LET otherD == nodeDesc[n] IN
    (* We can only offer help if we are actively trying to acquire nodes *)
    /\ descState[d] = "ACTIVE"
    /\ n \in descPending[d]
    (* The target node must be currently locked by a different descriptor otherD *)
    /\ nodeDesc[n] /= NULL
    /\ nodeDesc[n] /= d
    /\ IF descState[otherD] \in {"ACTIVE", "COMMITTING"}
       THEN (* If the competitor is in progress, advance its structure updates *)
            CommitStep(otherD)
       ELSE IF descState[otherD] \in {"SUCCESS", "ABORTED"}
       THEN (* If the competitor is done, help it unlock nodes and free memory *)
            ReleaseDescriptor(otherD)
       ELSE (* If otherD is IDLE, do nothing *)
            UNCHANGED vars

(****************************************************)
(* INVARIANTS AND PROPERTIES FOR VERIFICATION       *)
(****************************************************)
IsTree ==
    (* If any descriptor is actively executing step-by-step CommitStep, *)
    (* we allow temporary intermediate graph layouts until it transitions to SUCCESS *)
    IF \E d \in Descriptors : descState[d] = "COMMITTING"
    THEN 
        (* Even during commit, basic properties like anti-reflexivity must hold *)
        \A n \in Nodes : ~IsEdge(n, n)
    ELSE
        (* In stable states, the graph must strictly be a well-formed tree *)
        /\ \A p \in Nodes : ~IsEdge(p, 0)  (* 0 is the root node *)
        /\ \A n \in Nodes : n = 0 \/ n \in ReachableFrom(0)
        /\ \A n \in Nodes : n = 0 \/ Cardinality({p \in Nodes : IsEdge(p, n)}) = 1
        /\ \A n \in Nodes : ~IsEdge(n, n)

OperationTerminates ==
    \A d \in Descriptors : 
        (descState[d] \in {"ACTIVE", "COMMITTING", "SUCCESS", "ABORTED"}) 
            ~> (descState[d] = "IDLE")

GlobalProgress ==
    \E d \in Descriptors : descState[d] = "ACTIVE" ~> (descState[d] = "SUCCESS" \/ ~FreeStructConstraint)

(*******************************************)
(* NEXT STATE RELATION & SPECIFICATION     *)
(*******************************************)
Next ==
    \/ \E d \in Descriptors, frame \in SUBSET Nodes, linksMap \in [Nodes -> SUBSET Nodes] :
          /\ frame /= {}
          /\ IsValidFrame(frame)
          /\ CreateDescriptor(d, frame, linksMap)
    \/ \E d \in Descriptors, n \in Nodes : AcquireNode(d, n)
    \/ \E d \in Descriptors, n \in Nodes : Help(d, n)
    \/ \E d \in Descriptors : CommitStep(d)
    \/ \E d \in Descriptors : ReleaseDescriptor(d)

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A d \in Descriptors, n \in Nodes : WF_vars(AcquireNode(d, n))
    /\ \A d \in Descriptors, n \in Nodes : WF_vars(Help(d, n))
    /\ \A d \in Descriptors : WF_vars(CommitStep(d))
    /\ \A d \in Descriptors : WF_vars(ReleaseDescriptor(d))

========================================================================================
