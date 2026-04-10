----------------------------- MODULE MCAS -----------------------------
EXTENDS Integers, Sequences, TLC, FiniteSets

CONSTANTS Threads, Addresses, NULL

VARIABLES mem, announce, status, pc, targets

vars == <<mem, announce, status, pc, targets>>

Init == 
    /\ mem = [a \in Addresses |-> [val |-> 0, owner |-> NULL]]
    /\ announce = [t \in Threads |-> FALSE]
    /\ status = [t \in Threads |-> "Undecided"]
    /\ pc = [t \in Threads |-> "Idle"]
    /\ targets = [t \in Threads |-> {}]

TypeOK == 
    /\ \A t \in Threads : 
        /\ pc[t] \in {"Idle", "W_Acq", "W_Scan", "R_Ann", "R_Check", "Done"}
        /\ status[t] \in {"Undecided", "Committed", "Aborted"}
        /\ announce[t] \in {TRUE, FALSE}
        /\ targets[t] \subseteq Addresses
    /\ \A a \in Addresses : 
        /\ mem[a].owner \in Threads \cup {NULL}
        /\ mem[a].val \in {0, 1}

(***********************************************************************)
(* HELP: Thread helps other transaction to commit all its cells        *)
(***********************************************************************)
Help(t1, a) == 
    LET owner_id == mem[a].owner IN
    /\ pc[t1] \in {"W_Acq", "R_Check"}
    /\ owner_id /= NULL
    /\ pc[owner_id] = "W_Scan"
    /\ mem' = [addr \in Addresses |-> 
                IF mem[addr].owner = owner_id 
                THEN [val |-> 1, owner |-> NULL] 
                ELSE mem[addr]]
    /\ status' = [status EXCEPT ![owner_id] = "Committed"]
    /\ pc' = [pc EXCEPT ![owner_id] = "Done"]
    /\ UNCHANGED <<announce, targets>>

(***********************************************************************)
(* WRITER: Acquire Multiple -> Scan -> Commit All                      *)
(***********************************************************************)
Writer(t) == 
    \/ /\ pc[t] = "W_Acq"
       /\ \E ads \in SUBSET Addresses: ads /= {} /\ targets' = [targets EXCEPT ![t] = ads]
       /\ \A a \in targets'[t]: mem[a].owner = NULL
       /\ mem' = [a \in Addresses |-> 
                   IF a \in targets'[t]
                   THEN [mem[a] EXCEPT !.owner = t]
                   ELSE mem[a]]
       /\ pc' = [pc EXCEPT ![t] = "W_Scan"]
       /\ UNCHANGED <<announce, status>>
    \/ /\ pc[t] = "W_Scan"
       /\ status' = [status EXCEPT ![t] = "Committed"]
       /\ pc' = [pc EXCEPT ![t] = "Done"]
       /\ mem' = [a \in Addresses |-> 
                   IF mem[a].owner = t
                   THEN [val |-> 1, owner |-> NULL]
                   ELSE mem[a]]
       /\ UNCHANGED <<announce, targets>>

(***********************************************************************)
(* READER: Announce -> Read/Validate                                   *)
(***********************************************************************)
Reader(t, a) == 
    \/ /\ pc[t] = "R_Ann"
       /\ announce' = [announce EXCEPT ![t] = TRUE]
       /\ pc' = [pc EXCEPT ![t] = "R_Check"]
       /\ UNCHANGED <<mem, status, targets>>
    \/ /\ pc[t] = "R_Check"
       /\ mem[a].owner = NULL
       /\ pc' = [pc EXCEPT ![t] = "Done"]
       /\ announce' = [announce EXCEPT ![t] = FALSE]
       /\ UNCHANGED <<mem, status, targets>>

(***********************************************************************)
(* NEXT and INVARIANTS                                                 *)
(***********************************************************************)
StartWrite(t) == /\ pc[t] = "Idle" /\ pc' = [pc EXCEPT ![t] = "W_Acq"]
                 /\ UNCHANGED <<mem, announce, status, targets>>
StartRead(t)  == /\ pc[t] = "Idle" /\ pc' = [pc EXCEPT ![t] = "R_Ann"]
                 /\ UNCHANGED <<mem, announce, status, targets>>
Restart(t)    == /\ pc[t] = "Done" /\ pc' = [pc EXCEPT ![t] = "Idle"]
                 /\ UNCHANGED <<mem, announce, status, targets>>

Next == \E t \in Threads : 
            \/ Writer(t) 
            \/ StartWrite(t) \/ StartRead(t) \/ Restart(t)
            \/ \E a \in Addresses : Reader(t, a) \/ Help(t, a)

Spec == /\ Init /\ [][Next]_vars /\ WF_vars(Next)

Safety == \A r, w \in Threads : (/\ pc[r] = "Done" /\ pc[w] = "Done"
                                 /\ status[w] = "Committed") => (announce[r] = FALSE)

SystemProgress == []<>(\E t \in Threads : pc[t] = "Done")
=======================================================================
