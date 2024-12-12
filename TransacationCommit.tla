------------------------- MODULE TransacationCommit -------------------------
CONSTANT RM
VARIABLES rmState

TCTypeOK == rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]

Prepare(r) == /\ rmState[r] = "working"
              /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
              
Decide(r) == \/ /\ rmState[r] \in {"working", "prepared"}
                /\ \A s \in RM: rmState[s] # "committed"
                /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
             \/ /\ rmState[r] = "prepared"
                /\ \A s \in RM: rmState[s] \in {"prepared", "committed"}
                /\ rmState' = [rmState EXCEPT ![r]  = "committed"]   
               

TCInit == rmState = [r \in RM |-> "working"]

TCNext ==  \A r \in RM: Prepare(r) \/ Decide(r) 


TCConsistent ==  \A r1, r2 \in RM: ~ /\ rmState[r1] = "aborted"
                                     /\ rmState[r2] = "committed"


\*CONSTANT RM       \* The set of participating resource managers
\*VARIABLE rmState  \* `rmState[rm]' is the state of resource manager rm.
\*-----------------------------------------------------------------------------
\*TCTypeOK == 
\*  (*************************************************************************)
\*  (* The type-correctness invariant                                        *)
\*  (*************************************************************************)
\*  rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
\*
\*TCInit ==   rmState = [rm \in RM |-> "working"]
\*  (*************************************************************************)
\*  (* The initial predicate.                                                *)
\*  (*************************************************************************)
\*
\*canCommit == \A rm \in RM : rmState[rm] \in {"prepared", "committed"}
\*  (*************************************************************************)
\*  (* True iff all RMs are in the "prepared" or "committed" state.          *)
\*  (*************************************************************************)
\*
\*notCommitted == \A rm \in RM : rmState[rm] # "committed" 
\*  (*************************************************************************)
\*  (* True iff neither no resource manager has decided to commit.           *)
\*  (*************************************************************************)
\*-----------------------------------------------------------------------------
\*(***************************************************************************)
\*(* We now define the actions that may be performed by the RMs, and then    *)
\*(* define the complete next-state action of the specification to be the    *)
\*(* disjunction of the possible RM actions.                                 *)
\*(***************************************************************************)
\*Prepare(rm) == /\ rmState[rm] = "working"
\*               /\ rmState' = [rmState EXCEPT ![rm] = "prepared"]
\*
\*Decide(rm)  == \/ /\ rmState[rm] = "prepared"
\*                  /\ canCommit
\*                  /\ rmState' = [rmState EXCEPT ![rm] = "committed"]
\*               \/ /\ rmState[rm] \in {"working", "prepared"}
\*                  /\ notCommitted
\*                  /\ rmState' = [rmState EXCEPT ![rm] = "aborted"]
\*
\*TCNext == \E rm \in RM : Prepare(rm) \/ Decide(rm)
\*  (*************************************************************************)
\*  (* The next-state action.                                                *)
\*  (*************************************************************************)
\*-----------------------------------------------------------------------------
\*TCSpec == TCInit /\ [][TCNext]_rmState
\*  (*************************************************************************)
\*  (* The complete specification of the protocol.                           *)
\*  (*************************************************************************)
\*-----------------------------------------------------------------------------
\*(***************************************************************************)
\*(* We now assert invariance properties of the specification.               *)
\*(***************************************************************************)
\*TCConsistent ==  
\*  (*************************************************************************)
\*  (* A state predicate asserting that two RMs have not arrived at          *)
\*  (* conflicting decisions.                                                *)
\*  (*************************************************************************)
\*  \A rm1, rm2 \in RM : ~ /\ rmState[rm1] = "aborted"
\*                         /\ rmState[rm2] = "committed"
\*
\*THEOREM TCSpec => [](TCTypeOK /\ TCConsistent)
\*  (*************************************************************************)
\*  (* Asserts that TCTypeOK and TCConsistent are invariants of the protocol. *)
\*  (*************************************************************************)
\*=============================================================================

=============================================================================
\* Modification History
\* Last modified Thu Dec 05 14:20:32 AEDT 2024 by anisha
\* Created Wed Dec 04 20:04:26 AEDT 2024 by anisha
