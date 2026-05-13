------------------------------ MODULE TreeCAS ------------------------------
EXTENDS Integers, FiniteSets

(**************************************************************************************)
(* CONSTANTS AND TYPES: We will represent the tree as a set of nodes, which connected *)
(* to the structs. Structs are the other node's type, which consider on the structure *)
(* of children data. There are links loop: node -> struct -> node -> ...              *)
(**************************************************************************************)
CONSTANTS
    Nodes,        (* The set of all nodes, which does not change in this spec *)
    Structs,      (* The set of all available structs that store references to edges *)
    Descriptors,  (* The set of all available descriptors *)
    NULL

(***************************************************************************)
(* STATE VARIABLES                                                         *)
(***************************************************************************)
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
    freeStructs          (* Pool of available memory blocks for structs *)

vars == <<nodeStruct, nodeDesc, structLinks, descState, descPending, 
          descFrame, descExpectedStruct, descNewStruct, freeDescs, freeStructs>>

(***************************************************************************)
(* DYNAMIC GRAPH GEOMETRY                                                  *)
(***************************************************************************)
(* Checks if the struct of the parent node points to the child node *)
IsEdge(parent, child) == 
    child \in structLinks[nodeStruct[parent]]

RECURSIVE ReachableFrom(_, _)
ReachableFrom(src, visited) ==
    (* Find all unvisited direct children of the current node *)
    LET nextNodes == { child \in Nodes : IsEdge(src, child) /\ child \notin visited } IN
    IF nextNodes = {} 
    THEN 
        (* If no new children are found *)
        visited
    ELSE 
        (* To avoid unsafe UNION of sets, we sequentially accumulate reachability *)
        (* by choosing one child, expanding the visited set, and processing the rest *)
        LET chosenChild == CHOOSE x \in nextNodes : TRUE IN
        LET updatedVisited == ReachableFrom(chosenChild, visited \cup {chosenChild}) IN
        ReachableFrom(src, updatedVisited)

(* Validates if a set of nodes forms a valid connected frame in the current graph *)
IsValidFrame(f) ==
    /\ f /= {}
    /\ f \in SUBSET Nodes
    (* At least one "operation root" r must exist within the frame *)
    /\ \E r \in f :
        (* For any other node n within this frame *)
        /\ \A n \in f :
            (* n must be reachable from r exclusively through the nodes of this same frame *)
            n = r \/ n \in ReachableFrom(r, {r})

(***************************************************************************)
(* INITIALIZATION                                                          *)
(* Our goal is to verify node reachability when concurrent threads can     *)
(* delete a target node, potentially causing us to lose connection to      *)
(* the root. Therefore, it is sufficient to model the tree structure       *)
(* as a static pair of nodes: 0 -> 1.                                      *)
(***************************************************************************)
Init == 
    (* Expected set of nodes - 1 and 2 *)
    /\ {0, 1} \subseteq Nodes
    /\ Cardinality(Structs) >= 2
    (* Slots must be found for them in structs *)
    /\ \E s0 \in Structs, s1 \in Structs:
        /\ s0 /= s1
        (* Construct a small tree where 0 is the root and 1 is the child *)
        /\ nodeStruct = [n \in Nodes |-> IF n = 0 THEN s0 ELSE s1]
        /\ structLinks = [s \in Structs |-> IF s = s0 THEN {1} ELSE {}]
        /\ freeStructs = Structs \ {s0, s1}
    (* Initially all descriptors are empty *)
    /\ nodeDesc = [n \in Nodes |-> NULL]
    /\ descState = [d \in Descriptors |-> "IDLE"]
    /\ descPending = [d \in Descriptors |-> {}]
    /\ descFrame = [d \in Descriptors |-> {}]
    /\ descExpectedStruct = [d \in Descriptors |-> [n \in Nodes |-> NULL]]
    /\ descNewStruct = [d \in Descriptors |-> [n \in Nodes |-> NULL]]
    (* We will allocate the required ones if we want to start an operation *)
    /\ freeDescs = Descriptors

(***************************************************************************)
(* HELPER ACTIONS                                                          *)
(***************************************************************************)
ExecuteAcquire(d, n) ==
    (* We will need a function that marks nodes with our descriptor *)
    /\ nodeDesc' = [nodeDesc EXCEPT ![n] = d]
    /\ descPending' = [descPending EXCEPT ![d] = descPending[d] \ {n}]
    /\ UNCHANGED <<nodeStruct, structLinks, descState, descFrame, 
                   descExpectedStruct, descNewStruct, freeDescs, freeStructs>>

StartCommit(d) ==
    (* We will also need an operation that saves states after a successful *)
    (* frame replacement, performing value updates using other flush operations. *)
    /\ descState' = [descState EXCEPT ![d] = "COMMITTING"]
    /\ descPending' = [descPending EXCEPT ![d] = descFrame[d]]
    /\ UNCHANGED <<nodeStruct, nodeDesc, structLinks, descFrame, 
                   descExpectedStruct, descNewStruct, freeDescs, freeStructs>>

(***************************************************************************)
(* MAIN EVENTS (SYSTEM STEPS)                                              *)
(***************************************************************************)

(* 1) Create descriptor, pre-allocating new structs by excessively copying old ones *)
CreateDescriptor(d, frame, linksMap) ==
    /\ d \in freeDescs 
    /\ IsValidFrame(frame) 
    /\ Cardinality(freeStructs) >= Cardinality(frame)
    /\ \A n \in frame : linksMap[n] = structLinks[nodeStruct[n]]
    (* Allocate a set of structs sufficient to fill the frame *)
    /\ \E chosenStructs \in SUBSET freeStructs :
        /\ Cardinality(chosenStructs) = Cardinality(frame)
        /\ \E structMap \in [frame -> chosenStructs] :
            /\ \A s \in chosenStructs : \E n \in frame : structMap[n] = s
            /\ freeDescs' = freeDescs \ {d}
            /\ freeStructs' = freeStructs \ chosenStructs
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
            (* structs with the provided map data *)
            /\ structLinks' = [s \in Structs |-> IF s \in chosenStructs 
                                                 THEN linksMap[CHOOSE n \in frame : structMap[n] = s] 
                                                 ELSE structLinks[s]]
            /\ UNCHANGED <<nodeStruct, nodeDesc>>

(* 2) Attempt node acquisition via CAS with validation checks *)
AcquireNode(d, n) ==
    (* Ensure the descriptor is currently active and the target node still needs to be acquired *)
    /\ descState[d] = "ACTIVE" 
    /\ n \in descPending[d]
    (* Any parent node within the operation frame must be acquired first *)
    /\ \A parent \in descFrame[d] :
        IsEdge(parent, n) => nodeDesc[parent] = d
    /\ IF nodeStruct[n] /= descExpectedStruct[d][n]
       THEN (* The underlying node structure has changed since the descriptor creation. *)
            (* Abort the transaction to preserve consistency. *)
            /\ descState' = [descState EXCEPT ![d] = "ABORTED"]
            /\ UNCHANGED <<nodeStruct, nodeDesc, structLinks, descPending, 
                           descFrame, descExpectedStruct, descNewStruct, freeDescs, freeStructs>>
       ELSE IF nodeDesc[n] = NULL 
       THEN (* CAS SUCCESS: Lock the node *)
            ExecuteAcquire(d, n)
       ELSE (* CAS FAIL: Node is occupied *)
            UNCHANGED vars

(* 3 & 4) Step-by-step redirection of node pointers to redundant copied structs *)
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
                /\ UNCHANGED <<nodeDesc, descState, structLinks, descFrame, descExpectedStruct, descNewStruct, freeDescs, freeStructs>>
       ELSE IF descState[d] = "COMMITTING" /\ descPending[d] = {}
       THEN 
            (* All node redirects are complete and visible to the graph. *)
            /\ descState' = [descState EXCEPT ![d] = "SUCCESS"]
            /\ UNCHANGED <<nodeStruct, nodeDesc, structLinks, descPending, descFrame, descExpectedStruct, descNewStruct, freeDescs, freeStructs>>
       ELSE UNCHANGED vars

(* 5) Release locked nodes and return descriptor to the free pool *)
ReleaseDescriptor(d) ==
    /\ descState[d] \in {"SUCCESS", "ABORTED"} 
    /\ d \notin freeDescs
    /\ nodeDesc' = [n \in Nodes |-> IF nodeDesc[n] = d THEN NULL ELSE nodeDesc[n]]
    /\ descState' = [descState EXCEPT ![d] = "IDLE"]
    /\ freeDescs' = freeDescs \cup {d}
    /\ freeStructs' = freeStructs \cup 
                      (IF descState[d] = "ABORTED" 
                       THEN { descNewStruct[d][n] : n \in descFrame[d] } \ {nodeStruct[node] : node \in Nodes}
                       ELSE {})
    /\ UNCHANGED <<nodeStruct, structLinks, descPending, descFrame, descExpectedStruct, descNewStruct>>

(***************************************************************************)
(* GARBAGE COLLECTOR                                                       *)
(***************************************************************************)
GarbageCollect ==
    LET ActiveNodeStructs == {nodeStruct[n] : n \in Nodes} IN
    LET ActiveDescStructs == { s \in Structs : \E d \in Descriptors, n \in Nodes :
        /\ d \notin freeDescs
        /\ n \in descFrame[d]
        /\ descNewStruct[d][n] = s } IN
    LET ReferencedStructs == ActiveNodeStructs \cup ActiveDescStructs IN
    LET UnreferencedStructs == Structs \ ReferencedStructs IN
    /\ UnreferencedStructs \ freeStructs /= {}
    /\ freeStructs' = freeStructs \cup UnreferencedStructs
    /\ UNCHANGED <<nodeStruct, nodeDesc, structLinks, descState, 
                   descPending, descFrame, descExpectedStruct, descNewStruct, freeDescs>>

(***************************************************************************)
(* INVARIANTS AND PROPERTIES FOR VERIFICATION                              *)
(***************************************************************************)
TypeOK ==
    /\ nodeStruct \in [Nodes -> Structs]
    /\ nodeDesc \in [Nodes -> (Descriptors \cup {NULL})]
    /\ structLinks \in [Structs -> SUBSET Nodes]
    /\ descState \in [Descriptors -> {"IDLE", "ACTIVE", "COMMITTING", "SUCCESS", "ABORTED"}]
    /\ descPending \in [Descriptors -> SUBSET Nodes]
    /\ descFrame \in [Descriptors -> SUBSET Nodes]
    /\ descExpectedStruct \in [Descriptors -> [Nodes -> (Structs \cup {NULL})]]
    /\ descNewStruct \in [Descriptors -> [Nodes -> (Structs \cup {NULL})]]
    /\ freeDescs \in SUBSET Descriptors
    /\ freeStructs \in SUBSET Structs

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
        /\ \A n \in Nodes : n = 0 \/ n \in ReachableFrom(0, {0})
        /\ \A n \in Nodes : n = 0 \/ Cardinality({p \in Nodes : IsEdge(p, n)}) = 1
        /\ \A n \in Nodes : ~IsEdge(n, n)

OperationTerminates ==
    \A d \in Descriptors : 
        (descState[d] = "ACTIVE" \/ descState[d] = "COMMITTING") 
            ~> (descState[d] \in {"SUCCESS", "ABORTED"})

GlobalProgress ==
    (\E d \in Descriptors : descState[d] = "ACTIVE") 
        ~> (\E d \in Descriptors : descState[d] = "SUCCESS")

(***************************************************************************)
(* NEXT STATE RELATION & SPECIFICATION                                      *)
(***************************************************************************)
Next ==
    \/ \E d \in Descriptors, frame \in SUBSET Nodes, linksMap \in [Nodes -> SUBSET Nodes] :
          /\ frame /= {}
          /\ IsValidFrame(frame)
          /\ CreateDescriptor(d, frame, linksMap)
    \/ \E d \in Descriptors, n \in Nodes : AcquireNode(d, n)
    \/ \E d \in Descriptors : CommitStep(d)
    \/ \E d \in Descriptors : ReleaseDescriptor(d)
    \/ GarbageCollect

Spec == 
    /\ Init 
    /\ [][Next]_vars
    /\ \A d \in Descriptors, n \in Nodes : WF_vars(AcquireNode(d, n))
    /\ \A d \in Descriptors : WF_vars(CommitStep(d))
    /\ \A d \in Descriptors : WF_vars(ReleaseDescriptor(d))
    /\ WF_vars(GarbageCollect)

=============================================================================
