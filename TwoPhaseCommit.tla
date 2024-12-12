--------------------------- MODULE TwoPhaseCommit ---------------------------
\* In the model we consider any of the participating resoruces and Transactioin Manager can abort.
\* Resource Managers cannot commit unless told by Transaction Manager
\* TrasactionManager TM can commit only if all resouces are in prepared state
\* 
\*

CONSTANT RM
VARIABLES rmState, tmState, tmPrepared, msgs

Messages == [type: {"Prepared", "Aborted"}, r: RM] \union [type: {"Commit", "Abort"}]

TPTypeOK == 
            /\ rmState \in [RM -> {"working", "prepared", "committed", "aborted"}]
            /\ tmState \in {"init", "committed", "aborted"}
            /\ tmPrepared \subseteq RM
            /\ msgs \subseteq Messages

TPInit == /\ rmState = [r \in RM |-> "working"]
          /\ tmState = "init"
          /\ tmPrepared = {}
          /\ msgs = {}
            
TMRcvPrepared(r) == /\ tmState = "init"
                    /\ {r} \intersect tmPrepared = {}
                    /\ [type |-> "Prepared", r |-> r] \in msgs
                    /\ ~([type |-> "Aborted", r |-> r] \in msgs)
                    /\ tmPrepared' = tmPrepared \union {r}
                    /\ UNCHANGED<<rmState, msgs, tmState>>
                    
TMRcvAborted(r) ==  /\ tmState = "init"
                    /\ {r} \intersect tmPrepared = {}
                    /\ [type |-> "Aborted", r |-> r] \in msgs
                    /\ msgs' = msgs \union {[type |-> "Abort"]}
                    /\ tmState' = "aborted" 
                    /\ UNCHANGED<<rmState, tmPrepared>>

TMCommit == /\ tmState = "init"
            /\ ~([type |-> "Abort"] \in  msgs) 
            /\ tmPrepared = RM
            /\ msgs' = msgs \union {[type |-> "Commit"]}
            /\ tmState' = "committed"
            /\ UNCHANGED <<rmState, tmPrepared>>
            
TMAbort == /\ tmState = "init"
           /\ tmState' = "aborted"
           /\ msgs' = msgs \union {[type |-> "Abort"]}
           /\ UNCHANGED <<rmState, tmPrepared>>



RMSendPrepare(r) == /\ rmState[r] = "working"
                    /\ rmState' = [rmState EXCEPT ![r] = "prepared"]
                    /\ msgs' = msgs \union {[type |-> "Prepared", r |-> r]}
                    /\ UNCHANGED <<tmState, tmPrepared>>
                
RMSendAbort(r) ==   /\ rmState[r] = "working"
                    /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
                    /\ msgs' = msgs \union {[type |-> "Aborted", r |-> r]}
                    /\ UNCHANGED <<tmState, tmPrepared>>              
              
\*RMDecide(r) == \/ /\ rmState[r] \in {"working", "prepared"}
\*                  /\ \A s \in RM: rmState[s] # "committed"
\*                  /\ rmState' = [rmState EXCEPT ![r] = "aborted"]
\*               \/ /\ rmState[r] = "prepared"
\*                  /\ \A s \in RM: rmState[s] \in {"prepared", "committed"}
\*                  /\ rmState' = [rmState EXCEPT ![r]  = "committed"]   
               
RMReceiveCommit(r) == /\ rmState[r] = "prepared"
                      /\ \A s \in RM: rmState[s] \in {"prepared", "committed"}
                      /\ [type |-> "Commit"] \in msgs
                      /\ rmState' = [rmState EXCEPT ![r]  = "committed"]
                      /\ UNCHANGED <<tmState, tmPrepared, msgs>> 

RMReceiveAbort(r) ==  /\ rmState[r] \in {"prepared", "working"}
                      /\ [type |-> "Abort"] \in msgs
                      /\ rmState' = [rmState EXCEPT ![r]  = "aborted"]
                      /\ UNCHANGED <<tmState, tmPrepared, msgs>>

TPNext ==  \/ \E r \in RM: \/ RMSendPrepare(r) 
                           \/ RMSendAbort(r)
                           \/ RMReceiveCommit(r)
                           \/ RMReceiveAbort(r)
                           \/ TMRcvPrepared(r)
                           \/ TMRcvAborted(r)
           \/ TMCommit
           \/ TMAbort


TPConsistent ==  \A r1, r2 \in RM: ~ /\ rmState[r1] = "aborted"
                                     /\ rmState[r2] = "committed"
                                     
TPSpec == TPInit /\ [][TPNext]_<<rmState, tmState, tmPrepared, msgs>>

THEOREM TPSpec => [](TPTypeOK /\ TPConsistent)

=============================================================================
\* Modification History
\* Last modified Sat Dec 07 15:42:48 AEDT 2024 by anisha
\* Created Thu Dec 05 14:32:51 AEDT 2024 by anisha
