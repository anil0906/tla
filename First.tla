------------------------------- MODULE First -------------------------------
EXTENDS Integers
VARIABLES i, pc

Init == i = 0 /\ pc = "start"

Pick == /\ pc = "start"
        /\ i' \in 0..1000
        /\ pc' = "middle"
 
Add1 == /\ pc = "middle"
        /\ i' = i + 1
        /\ pc' = "end"

Next == \/ Pick
        \/ Add1



=============================================================================
\* Modification History
\* Last modified Wed Dec 04 19:15:22 AEDT 2024 by anisha
\* Created Wed Dec 04 18:56:37 AEDT 2024 by anisha
