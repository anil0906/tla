------------------------------- MODULE zerokv -------------------------------
EXTENDS Integers, Sequences

CONSTANT Nodes, Keys

VARIABLES nState, checkpoint, abcast, abcastPurgedOffset
\* message has fields: key, value, version, snapshotVersion 
Messages == [key: Keys, value: Nat, version: Nat, snapshotVersion: Nat \union {0}]

\* Data to be stored in each node. Check TypeOK for details.
\* Data is stored in the form of sequence againt valueMap field. TODO: Store in Record format
Data == [key: Keys, value: Nat, version: Nat, snapshotVersion: Nat \union {0}] \union {}



TypeOK == /\ \A i \in DOMAIN abcast: {abcast[i]} \subseteq Messages
          /\ nState \in [Nodes -> [valueMap: Seq(Data), snapshotVersion: Nat \union {0}, leastSnapshotVersion: Nat \union {0}, leastInstalledVersion: Nat \union {0}]]
          /\ checkpoint >= abcastPurgedOffset
          /\ checkpoint \in Nat \union {0}
          /\ abcastPurgedOffset \in Nat \union {0}

ASSUME Keys \subseteq Nat

                                  
\* Helper function to find minimum of two versions. This is used to update the checkpoint. min (leastSnapshotVersion, leastInstalledVersion)

ChooseLeast(x, y) == IF x < y THEN x ELSE y 

\* Helper function to check if key exist in valueMap sequence.

IfDataInSeq(seq, key) == \E i \in DOMAIN seq: seq[i].key = key

\* Helper function to return tuple of boolean flag and index of the specific key in valueMap sequence. If record does not exist index will be -1;

FindDataInSeq(seq, key) == LET exist == IfDataInSeq(seq, key)  
                               index == IF exist THEN CHOOSE i \in DOMAIN seq: seq[i].key = key ELSE -1
                           IN <<exist, index>>
                              
\* Helper function to return index from valueMap sequence based on given field predicate.
\* This is used to find leastSnapshotVersion and leastInstalledVersion on succeful replication.

Minimum(seq, field) == CHOOSE s1 \in DOMAIN seq: \A s2 \in DOMAIN seq: seq[s1][field] <= seq[s2][field] 
                                                       

\* Helper function to make sure we only one entry for a given key in a valueMap sequence.

Upsert(seq, record) == LET result == FindDataInSeq(seq, record.key)
                           exist == result[1] 
                           index == result[2]     
                       IN IF ~exist THEN Append(seq, record) 
                          ELSE IF index = 1 THEN <<record>> \o SubSeq(seq, index+1, Len(seq))
                          ELSE IF index = Len(seq) THEN SubSeq(seq, 1, index - 1) \o <<record>>
                          ELSE SubSeq(seq, 1, index - 1) \o <<record>> \o SubSeq(seq, index+1, Len(seq))
                                    

\* State update Helper funtion in case of Abort transaction. This is used  in  NodeRecvMessage Operator.                                                    
AbortStateUpdate(n, msg) == nState' = [nState EXCEPT ![n].snapshotVersion = msg.version]

\* State update Helper funtion in case of Commit transaction. This is used  in  NodeRecvMessage Operator. 
CommitStateUpdate(n, msg) ==  /\ LET value == [key |-> msg.key, value |-> msg.value, snapshotVersion |-> msg.snapshotVersion, version |-> msg.version]
                                     existingValueMap == nState[n].valueMap
                                     updatedValueMap == Upsert(existingValueMap, value) 
                                     minimumSnapshotIndex == Minimum(updatedValueMap, "snapshotVersion") \* Note merged valueMap ise used to calculate 
                                     minimumInstalledVersionIndex == Minimum(updatedValueMap, "version")  \* leastSnapshotVersion and leastInstalledversion
                                 IN /\ nState' = [nState EXCEPT ![n].snapshotVersion = msg.version,
                                                             ![n].leastSnapshotVersion = updatedValueMap[minimumSnapshotIndex]["snapshotVersion"],
                                                             ![n].leastInstalledVersion = updatedValueMap[minimumSnapshotIndex]["version"],
                                                             ![n].valueMap = updatedValueMap]                        


                               

\* State Update Helper function on publishing to abcast. This is used in NodeUpdateMsg and NodeInsertMsg Operators.

SendToAbcast(m) == abcast' = abcast \o <<m>>

\* InsertRecort: Operator to publish to abcast after local checks. We check locally if key does not exist before proceeding with insert operation. TODO: We will remove the local checks to see if certification still pass.

NodeInsertMsg(n, key) == /\ ~IfDataInSeq(nState[n].valueMap, key)
                         /\ SendToAbcast([key |-> key,
                                          value |-> 1,
                                          version |-> abcastPurgedOffset + Len(abcast) + 1,
                                          snapshotVersion |-> nState[n].snapshotVersion])
                                                
                         /\ UNCHANGED <<nState, checkpoint, abcastPurgedOffset>>
                                          
\* UpdateRecord: Operator to publish to abcast after local checks. We check in local state if key exist before publishing to abcast.

NodeUpdateMsg(n, key) == /\ LET result == FindDataInSeq(nState[n].valueMap, key)
                                exist == result[1] 
                                index == result[2] 
                            IN /\ exist
                               /\ SendToAbcast([key |-> key,
                                                   value |-> nState[n].valueMap[index].value + 1, \* Add to previous value
                                                   version |-> abcastPurgedOffset + Len(abcast) + 1,
                                                   snapshotVersion |-> nState[n].snapshotVersion])
                         /\ UNCHANGED <<nState, checkpoint, abcastPurgedOffset>>
                         
\* Update Checkpoint based on leastSnapshotVersion and leastSnapshotVersion
\* Reasoning: If we have any record where really old snapshotVersion was submitted. May be the really slow node tries to update rarely updated record.
\* In this case we would need this record as we won't know if there is any future transaction that might rely on this version to certify.
\* Once we publish this to abcast and replicate back it will update the leastSnapshotVersion in localState and checkpoint can keep moving further.
\* We also check the leastVersion in localState as we cannot move our checkpoint beyond oldest record.
\* Either case could happen so we set checkpoint to min (leastSnapshotVersion and leastInstalledVersion

NodeUpdateCheckpoint(n) ==  /\ LET leastVersion == ChooseLeast(nState[n].leastSnapshotVersion,nState[n].leastInstalledVersion)
                               IN /\ leastVersion > checkpoint
                                  /\ checkpoint' = leastVersion
                            /\ UNCHANGED <<nState, abcast, abcastPurgedOffset>>  
                              
\* TODO: Not required right now.
\*NodeRePublishOldestRecord(n) == /\ LET leastVersion == ChooseLeast(nState[n].leastSnapshotVersion,nState[n].leastInstalledVersion)
\*                                   IN /\ leastVersion > checkpoint
\*                                      /\ checkpoint' = leastVersion
\*                                /\ UNCHANGED <<nState, abcast, abcastPurgedOffset>> 
                              
NodeReset(n) == /\ nState' = [nState EXCEPT ![n] = [snapshotVersion |-> 0, leastSnapshotVersion |-> 0, leastInstalledVersion |-> 0, valueMap |-> <<>>]]
                /\ UNCHANGED <<abcast, checkpoint, abcastPurgedOffset>>
                         
AbcastPurge == /\ Len(abcast) > 0
               /\ abcastPurgedOffset = Head(abcast).version - 1
               /\ checkpoint > abcastPurgedOffset
               \* This is not required. As consumer has handled this case. If purging happens while lagging node is still behind checkpoint. 
\*               /\ \A n \in Nodes: nState[n].snapshotVersion > checkpoint \* Only purge if there are no consumers below the checkpoint.
               /\ abcastPurgedOffset' = checkpoint - 1
               /\ abcast' = SubSeq(abcast, checkpoint - abcastPurgedOffset, Len(abcast)) \* SubSeq(seq, m, n) returns sub sequence from m through n both m and n inclusive
               /\ UNCHANGED <<nState, checkpoint>>

GetLastReadIndex(n) == IF checkpoint # 0 /\ nState[n].snapshotVersion = 0
                       THEN IF checkpoint > abcastPurgedOffset \* checkpoint is available but data is not yet purged.
                            THEN checkpoint - abcastPurgedOffset - 1
                            ELSE 0
                       ELSE nState[n].snapshotVersion \* THEN path is only taken when node goes does down and check poinit exist. Rest of the cases it will go through next message in else.
                    

NodeRecvMessage(n) ==   /\ Len(abcast) > 0 \* Atleast one message exist in abcast
                        \* New message exist to receive. 
                        \* This also handles the case if abcast got purged even if some node is lagging behind.
                        /\ nState[n].snapshotVersion < abcast[Len(abcast)].version
                        /\ LET readOffset == GetLastReadIndex(n)
                               msg == abcast[readOffset + 1]
                               result == FindDataInSeq(nState[n].valueMap, msg.key)
                               exist == result[1]
                               index == result[2]
                           IN \/ /\ exist
                                 /\ \/ /\ nState[n].valueMap[index].version > msg.snapshotVersion \* Abort: No installation
                                       /\ AbortStateUpdate(n, msg)
                                    \/ /\ nState[n].valueMap[index].version < msg.snapshotVersion
                                       /\ CommitStateUpdate(n, msg)
                              \/ CommitStateUpdate(n, msg)      
                        /\ UNCHANGED <<abcast, checkpoint, abcastPurgedOffset>>      
                                    
Init == /\ checkpoint = 0 \* 0 means no check point recorded.
        /\ nState = [n \in Nodes |-> [snapshotVersion |-> 0, leastSnapshotVersion |-> 0, leastInstalledVersion |-> 0, valueMap |->  <<>> ]]
        /\ abcast = <<>>
        /\ abcastPurgedOffset = 0
        
Next == \/ AbcastPurge
        \/ \E n \in Nodes: \/ \E k \in Keys: \/ NodeInsertMsg(n,k)
                                             \/ NodeUpdateMsg(n,k)
                           \/ NodeUpdateCheckpoint(n)
                           \/ NodeReset(n)
                           \/ NodeRecvMessage(n)



Consistent == \E n1, n2 \in Nodes: \/ /\ nState[n1].snapshotVersion = nState[n2].snapshotVersion 
                                      /\ nState[n1].valueMap = nState[n2].valueMap
                                   \/ nState[n1].snapshotVersion # nState[n2].snapshotVersion 
                         
Spec == Init /\ [][Next]_<<nState, abcast, checkpoint, abcastPurgedOffset>>

THEOREM Spec => [](TypeOK /\ Consistent)

=============================================================================
\* Modification History
\* Last modified Thu Dec 12 11:51:10 AEDT 2024 by anisha
\* Created Mon Dec 09 21:28:40 AEDT 2024 by anisha
