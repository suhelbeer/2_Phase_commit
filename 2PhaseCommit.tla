------------------------------- MODULE proj1 -------------------------------
EXTENDS Integers, Sequences, FiniteSets, TLC
CONSTANT RM,         \* The set of participating resource managers RM=1..3 
         TMMAYFAIL,    \* Whether TM may fail
         RMMAYFAIL

(***************************************************************************
\* Write your code only in this block 
\* The only thing you need to update in TLA+ is the properties, for the rest use PlusCal
--fair algorithm 2PC {
variable rmState = [rm \in RM |-> "working"],
         tmState = "init";
  
define {
   canCommit ==    \A rm \in RM  : rmState[rm] \in {"prepared"} \/ \E rm2 \in RM : rmState[rm2] \in {"committed"}
   canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted","unavailable"} /\  ~ \E rm2 \in RM : rmState[rm2] \in {"committed"}
}



  fair process (RManager \in RM)
  variables pre="";{
RS:  while (rmState[self] \in {"working", "prepared","unavailable"}) { 
        either { 
           await rmState[self] = "working";
           rmState[self] := "prepared" ; } 
        or { 
           await rmState[self]="prepared" /\ tmState="commit";
RC:        rmState[self] := "committed";}
        or {
           await rmState[self]="working" 
            \/  (rmState[self]="prepared" /\ tmState="abort");
RA:        rmState[self] := "aborted";}       
         or {
           await RMMAYFAIL /\ pre="";
           pre := rmState[self];
RU:        rmState[self] := "unavailable";}
         or {
           await RMMAYFAIL /\ pre/="";
           rmState[self] := pre;
RR:        pre:=""}
     }                 
  }


   
  fair process (TManager=0) {
TM:  either 
      { await canCommit;
        tmState := "commit";
F1:     if (TMMAYFAIL) tmState := "unavailable";}         
     or 
      { await canAbort;
        tmState := "abort";
F2:     if (TMMAYFAIL) tmState := "unavailable";}  
  }
  
  
  fair process (BTManager=10) {
BTM:  either 
      { await (tmState = "unavailable" /\ canCommit);
BTC:       tmState := "commit";}
     or 
      { await (tmState = "unavailable" /\  canAbort);
BTA:       tmState := "abort";}
  }



}

***************************************************************************)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-55174e89ff0de58f2ab8bb1682ecd811
VARIABLES rmState, tmState, pc

(* define statement *)
canCommit ==    \A rm \in RM  : rmState[rm] \in {"prepared"} \/ \E rm2 \in RM : rmState[rm2] \in {"committed"}
canAbort ==     \E rm \in RM : rmState[rm] \in {"aborted","unavailable"} /\  ~ \E rm2 \in RM : rmState[rm2] \in {"committed"}

VARIABLE pre

vars == << rmState, tmState, pc, pre >>

ProcSet == (RM) \cup {0} \cup {10}

Init == (* Global variables *)
        /\ rmState = [rm \in RM |-> "working"]
        /\ tmState = "init"
        (* Process RManager *)
        /\ pre = [self \in RM |-> ""]
        /\ pc = [self \in ProcSet |-> CASE self \in RM -> "RS"
                                        [] self = 0 -> "TM"
                                        [] self = 10 -> "BTM"]

RS(self) == /\ pc[self] = "RS"
            /\ IF rmState[self] \in {"working", "prepared","unavailable"}
                  THEN /\ \/ /\ rmState[self] = "working"
                             /\ rmState' = [rmState EXCEPT ![self] = "prepared"]
                             /\ pc' = [pc EXCEPT ![self] = "RS"]
                             /\ pre' = pre
                          \/ /\ rmState[self]="prepared" /\ tmState="commit"
                             /\ pc' = [pc EXCEPT ![self] = "RC"]
                             /\ UNCHANGED <<rmState, pre>>
                          \/ /\      rmState[self]="working"
                                \/  (rmState[self]="prepared" /\ tmState="abort")
                             /\ pc' = [pc EXCEPT ![self] = "RA"]
                             /\ UNCHANGED <<rmState, pre>>
                          \/ /\ RMMAYFAIL /\ pre[self]=""
                             /\ pre' = [pre EXCEPT ![self] = rmState[self]]
                             /\ pc' = [pc EXCEPT ![self] = "RU"]
                             /\ UNCHANGED rmState
                          \/ /\ RMMAYFAIL /\ pre[self]/=""
                             /\ rmState' = [rmState EXCEPT ![self] = pre[self]]
                             /\ pc' = [pc EXCEPT ![self] = "RR"]
                             /\ pre' = pre
                  ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << rmState, pre >>
            /\ UNCHANGED tmState

RC(self) == /\ pc[self] = "RC"
            /\ rmState' = [rmState EXCEPT ![self] = "committed"]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED << tmState, pre >>

RA(self) == /\ pc[self] = "RA"
            /\ rmState' = [rmState EXCEPT ![self] = "aborted"]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED << tmState, pre >>

RU(self) == /\ pc[self] = "RU"
            /\ rmState' = [rmState EXCEPT ![self] = "unavailable"]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED << tmState, pre >>

RR(self) == /\ pc[self] = "RR"
            /\ pre' = [pre EXCEPT ![self] = ""]
            /\ pc' = [pc EXCEPT ![self] = "RS"]
            /\ UNCHANGED << rmState, tmState >>

RManager(self) == RS(self) \/ RC(self) \/ RA(self) \/ RU(self) \/ RR(self)

TM == /\ pc[0] = "TM"
      /\ \/ /\ canCommit
            /\ tmState' = "commit"
            /\ pc' = [pc EXCEPT ![0] = "F1"]
         \/ /\ canAbort
            /\ tmState' = "abort"
            /\ pc' = [pc EXCEPT ![0] = "F2"]
      /\ UNCHANGED << rmState, pre >>

F1 == /\ pc[0] = "F1"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "unavailable"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << rmState, pre >>

F2 == /\ pc[0] = "F2"
      /\ IF TMMAYFAIL
            THEN /\ tmState' = "unavailable"
            ELSE /\ TRUE
                 /\ UNCHANGED tmState
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << rmState, pre >>

TManager == TM \/ F1 \/ F2

BTM == /\ pc[10] = "BTM"
       /\ \/ /\ (tmState = "unavailable" /\ canCommit)
             /\ pc' = [pc EXCEPT ![10] = "BTC"]
          \/ /\ (tmState = "unavailable" /\  canAbort)
             /\ pc' = [pc EXCEPT ![10] = "BTA"]
       /\ UNCHANGED << rmState, tmState, pre >>

BTC == /\ pc[10] = "BTC"
       /\ tmState' = "commit"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, pre >>

BTA == /\ pc[10] = "BTA"
       /\ tmState' = "abort"
       /\ pc' = [pc EXCEPT ![10] = "Done"]
       /\ UNCHANGED << rmState, pre >>

BTManager == BTM \/ BTC \/ BTA

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == TManager \/ BTManager
           \/ (\E self \in RM: RManager(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(Next)
        /\ \A self \in RM : WF_vars(RManager(self))
        /\ WF_vars(TManager)
        /\ WF_vars(BTManager)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-b497cefd9715284033cfadd3166ee33c






Consistency ==  
  (*************************************************************************)
  (* A state predicate asserting that two RMs have not arrived at          *)
  (* conflicting decisions.                                                *)
  (*************************************************************************)
  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
                         /\ rmState[rm2] = "committed"

Completed == <> (\A rm \in RM : rmState[rm] \in {"committed","aborted"}) 

NotCommitted == \A rm \in RM : rmState[rm] # "committed" 

TypeOK == 
  (*************************************************************************)
  (* The type-correctness invariant                                        *)
  (*************************************************************************)
  /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
  /\ tmState \in {"init", "commit", "abort", "unavailable"}

=============================================================================
\* Modification History
\* Last modified Fri Jun 12 19:04:52 EDT 2020 by asus
\* Last modified Tue Jun 02 15:47:07 EDT 2020 by bekir
\* Created Tue Jun 02 15:29:01 EDT 2020 by bekir
\* Taken from Dr. Demirbas's 2PC implementation in his lecture slides
