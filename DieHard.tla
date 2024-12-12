------------------------------ MODULE DieHard ------------------------------

EXTENDS Integers
VARIABLES small, big

Init == small = 0 /\ big = 0

FillSmall == small' = 3 /\ big' = big

FillBig == big' = 5 /\ small' = small

EmptySmall == small' = 0 /\ big' = big

EmptyBig == big' = 0 /\ small' = small

SmallToBig == \/ /\ small + big >= 5
                 /\ small' = big - 5 + small
                 /\ big' = 5
              \/ /\ small + big < 5
                 /\ small' = 0
                 /\ big' = big + small      

BigToSmall == \/ /\ small + big >= 3
                 /\ small' = 3
                 /\ big' = big + small - 3
              \/ /\ small + big < 3
                 /\ small' = small + big
                 /\ big' = 0
                 
Next == \/ FillSmall
        \/ FillBig
        \/ EmptySmall
        \/ EmptyBig
        \/ SmallToBig
        \/ BigToSmall
        
        
TypeOK == small \in 0..3 /\ big \in 0..5                 

=============================================================================
\* Modification History
\* Last modified Wed Dec 04 19:56:59 AEDT 2024 by anisha
\* Created Wed Dec 04 19:31:01 AEDT 2024 by anisha
