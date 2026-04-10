----------------------------- MODULE MCAS -----------------------------
EXTENDS Integers, Sequences, TLC

CONSTANTS Threads, Addresses, NULL

VARIABLES
    mem,      \* [addr   -> [val, owner]]
    announce, \* [thread -> boolean]
    status,   \* [thread -> {Undecided, Committed, Aborted}]
    pc   \* [thread -> {Idle, W\_Acq, W\_Scan, R\_Ann, R\_Check, Done}]

vars == <<mem, announce, status, pc>>

Init ==
    /\ mem = [a \in Addresses |-> [val |-> 0, owner |-> NULL]]
    /\ announce = [t \in Threads |-> FALSE]
    /\ status = [t \in Threads |-> "Undecided"]
    /\ pc = [t \in Threads |-> "Idle"]

TypeOK ==
    /\ \A t \in Threads :
        /\ pc[t] \in {"Idle", "W_Acq", "W_Scan",
                      "R_Ann", "R_Check", "Done"}
        /\ status[t] \in
                     {"Undecided", "Committed", "Aborted"}
        /\ announce[t] \in {TRUE, FALSE}
    /\ \A a \in Addresses :
        /\ mem[a].owner \in Threads \cup {NULL}
        /\ mem[a].val \in {0, 1}

(***********************************************************************)
(* HELP: Thread helps other transaction                                *)
(***********************************************************************)
Help(t1, a) ==
    LET owner_id == mem[a].owner IN
    /\ pc[t1] \in {"W_Acq", "R_Check"}
    /\ owner_id /= NULL
    /\ pc[owner_id] = "W_Scan"
    \* Physical commit on behalf of the owner:
    /\ mem' = [mem EXCEPT ![a] = [val |-> 1,
                                  owner |-> NULL]]
    /\ status' = [status EXCEPT ![owner_id] = "Committed"]
    /\ pc' = [pc EXCEPT ![owner_id] = "Done"]
    /\ UNCHANGED announce

(***********************************************************************)
(* WRITER: Acquire -> Scan -> Commit -> Release                        *)
(***********************************************************************)
Writer(t, a) ==
    \/ /\ pc[t] = "W_Acq"  /\ mem[a].owner = NULL
       /\ mem' = [mem EXCEPT ![a].owner = t]
       /\ pc' = [pc EXCEPT ![t] = "W_Scan"]
       /\ UNCHANGED <<announce, status>>

    \/ /\ pc[t] = "W_Scan"
       /\ status' = [status EXCEPT ![t] = "Committed"]
       /\ pc' = [pc EXCEPT ![t] = "Done"]
       /\ mem' = [mem EXCEPT ![a] = [val |-> 1,
                                     owner |-> NULL]]
       /\ UNCHANGED announce

(***********************************************************************)
(* READER: Announce -> Read/Validate                                   *)
(***********************************************************************)
Reader(t, a) ==
    \/ /\ pc[t] = "R_Ann"
       /\ announce' = [announce EXCEPT ![t] = TRUE]
       /\ pc' = [pc EXCEPT ![t] = "R_Check"]
       /\ UNCHANGED <<mem, status>>

    \/ /\ pc[t] = "R_Check"
       /\ mem[a].owner = NULL
       /\ pc' = [pc EXCEPT ![t] = "Done"]
       /\ announce' = [announce EXCEPT ![t] = FALSE]
       /\ UNCHANGED <<mem, status>>

(***********************************************************************)
(* NEXT and INVARIANTS                                                 *)
(***********************************************************************)
StartWrite(t) ==
    /\ pc[t] = "Idle" /\ pc' = [pc EXCEPT ![t] = "W_Acq"]
    /\ UNCHANGED <<mem, announce, status>>

StartRead(t) ==
    /\ pc[t] = "Idle" /\ pc' = [pc EXCEPT ![t] = "R_Ann"]
    /\ UNCHANGED <<mem, announce, status>>

Restart(t) ==
    /\ pc[t] = "Done" /\ pc' = [pc EXCEPT ![t] = "Idle"]
    /\ UNCHANGED <<mem, announce, status>>

Next == \E t \in Threads, a \in Addresses :
    \/ Writer(t, a) \/ Reader(t, a) \/ Help(t, a)
    \/ StartWrite(t) \/ StartRead(t) \/ Restart(t)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

Safety ==
    \A r, w \in Threads : (/\ pc[r] = "Done"
                           /\ pc[w] = "Done"
                           /\ status[w] = "Committed")
    => (announce[r] = FALSE)

SystemProgress == []<>(\E t \in Threads : pc[t] = "Done")

THEOREM Spec => []Safety /\ SystemProgress
<1>1. Spec => []Safety
    BY DEF Spec, Init, Safety, Next, Writer, Reader, vars
<1>2. Spec => SystemProgress
    BY DEF Spec, Next, Writer, Reader, vars
<1>3. QED BY <1>1, <1>2
========================================================================