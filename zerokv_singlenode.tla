------------------------- MODULE zerokv_singlenode -------------------------

EXTENDS Integers, Sequences
    
CONSTANT Keys

VARIABLES nodeState, checkpoint, abcast, stateSnapshots, runCounter 
\* message has fields: key, value, version, snapshotVersion 
Messages == [key: Keys, value: Nat, version: Nat, snapshotVersion: Nat \union {0}]

\* Data to be stored in each node. Check TypeOK for details.
\* Data is stored in the form of sequence againt valueMap field. TODO: Store in Record format
Data == [key: Keys, value: Nat, version: Nat, snapshotVersion: Nat \union {0}] \union {}


TypeOK == /\ \A i \in DOMAIN abcast: {abcast[i]} \subseteq Messages
          /\ nodeState \in [valueMap: Seq(Data), snapshotVersion: Nat \union {0}, leastSnapshotVersion: Nat \union {0}, leastInstalledVersion: Nat \union {0}, lastProcessedVersion: Nat \union {0}]    
          /\ checkpoint \in Nat \union {0}
          /\ runCounter \in Nat
          /\ stateSnapshots \in Seq([valueMap: Seq(Data), snapshotVersion: Nat \union {0}, runCounter: Nat])
          
         
DataInvariant == /\ checkpoint <= Len(abcast)
                 /\ \/ nodeState.leastInstalledVersion = 0 /\ nodeState.leastSnapshotVersion = 0
                    \/ nodeState.leastSnapshotVersion < nodeState.leastInstalledVersion

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
\* Why do we update snapshot version in case of Abort?
\* This is required to make progress now. As We are getting message after lastProcessedState                                              
AbortStateUpdate(msg) == /\ nodeState' = [nodeState EXCEPT !.lastProcessedVersion = msg.version]
                         /\ UNCHANGED <<abcast, checkpoint, runCounter, stateSnapshots>>

\* State update Helper funtion in case of Commit transaction. This is used  in  NodeRecvMessage Operator. 
CommitStateUpdate(msg) ==  /\ LET value == [key |-> msg.key, value |-> msg.value, snapshotVersion |-> msg.snapshotVersion, version |-> msg.version]
                                  existingValueMap == nodeState.valueMap
                                  updatedValueMap == Upsert(existingValueMap, value) 
                                  minimumSnapshotIndex == Minimum(updatedValueMap, "snapshotVersion") \* Note merged valueMap ise used to calculate 
                                  minimumInstalledVersionIndex == Minimum(updatedValueMap, "version")  \* leastSnapshotVersion and leastInstalledversion
                                  newNodeState == [snapshotVersion |-> msg.version,
                                                   lastProcessedVersion |-> msg.version, 
                                                   leastSnapshotVersion |-> updatedValueMap[minimumSnapshotIndex]["snapshotVersion"],
                                                   leastInstalledVersion |-> updatedValueMap[minimumSnapshotIndex]["version"],
                                                   valueMap |-> updatedValueMap]
                               IN /\ nodeState' = newNodeState
                                  /\ stateSnapshots' = stateSnapshots \o <<[valueMap|-> updatedValueMap, snapshotVersion|-> msg.version, runCounter|-> runCounter]>>                         
                            /\ UNCHANGED <<abcast, checkpoint, runCounter>>

                               

\* State Update Helper function on publishing to abcast. This is used in NodeUpdateMsg and NodeInsertMsg Operators.

SendToAbcast(m) == abcast' = abcast \o <<m>>

\* InsertRecort: Operator to publish to abcast after local checks. We check locally if key does not exist before proceeding with insert operation. TODO: We will remove the local checks to see if certification still pass.

NodeInsertMsg(key) == /\ ~IfDataInSeq(nodeState.valueMap, key)
                      /\ SendToAbcast([key |-> key,
                                       value |-> 1,
                                       version |-> Len(abcast) + 1,
                                       snapshotVersion |-> nodeState.snapshotVersion])
                                                
                         /\ UNCHANGED <<nodeState, checkpoint, runCounter, stateSnapshots>>
                                          
\* UpdateRecord: Operator to publish to abcast after local checks. We check in local state if key exist before publishing to abcast.

NodeUpdateMsg(key) == /\ LET result == FindDataInSeq(nodeState.valueMap, key)
                             exist == result[1] 
                             index == result[2] 
                         IN /\ exist
                            /\ SendToAbcast([key |-> key,
                                             value |-> nodeState.valueMap[index].value + 1, \* Add to previous value
                                             version |-> Len(abcast) + 1,
                                             snapshotVersion |-> nodeState.snapshotVersion])
                         /\ UNCHANGED <<nodeState, checkpoint, runCounter, stateSnapshots>>
                         
\* Update Checkpoint based on leastSnapshotVersion and leastInstalledVersion
\* Update: We are just checking leastSnapshotVersion as snapshot version submitted with a record will always be less than the version itself. 

NodeUpdateCheckpoint ==  /\ checkpoint < nodeState.leastSnapshotVersion
                         /\ checkpoint' = nodeState.leastSnapshotVersion
                         /\ UNCHANGED <<nodeState, abcast, runCounter, stateSnapshots>>  
                              
\* TODO: Not required right now.
\*NodeRePublishOldestRecord(n) == /\ LET leastVersion == ChooseLeast(nState[n].leastSnapshotVersion,nState[n].leastInstalledVersion)
\*                                   IN /\ leastVersion > checkpoint
\*                                      /\ checkpoint' = leastVersion
\*                                /\ UNCHANGED <<nState, abcast, abcastPurgedOffset>> 
                              
NodeReset == /\ nodeState' = [snapshotVersion |-> 0, leastSnapshotVersion |-> 0, leastInstalledVersion |-> 0, valueMap |-> <<>>,lastProcessedVersion |-> 0]
             /\ runCounter' = runCounter + 1
             /\ UNCHANGED <<abcast, checkpoint, stateSnapshots>>
                         

NodeRecvMessage ==      /\ Len(abcast) > 0 \* Atleast one message exist in abcast
                                               
                        /\ nodeState.lastProcessedVersion < Len(abcast) \* Atleast one New message exist to receive.
                        
                        /\ LET NextIndexToRead == IF checkpoint # 0 /\ nodeState.lastProcessedVersion = 0 \* Node being reset.
                                                  THEN checkpoint
                                                  ELSE nodeState.lastProcessedVersion + 1
                               msg == abcast[NextIndexToRead] 
                               result == FindDataInSeq(nodeState.valueMap, msg.key)
                               exist == result[1]
                               index == result[2]
                           IN \/ /\ exist
                                 /\ \/ /\ nodeState.valueMap[index].version > msg.snapshotVersion \* Abort: No installation of valueMap. Only update lastProcessedVersion
                                       /\ AbortStateUpdate(msg)
                                    \/ /\ nodeState.valueMap[index].version <= msg.snapshotVersion
                                       /\ CommitStateUpdate(msg)
                              \/ /\ ~exist
                                 /\ LET versionToCompare == IF nodeState.snapshotVersion = 0 \* Either first message from abcast or first message after node reset starting from checkpoint.
                                                            THEN checkpoint
                                                            ELSE nodeState.snapshotVersion  
                                    IN \/ /\ msg.snapshotVersion >= versionToCompare
                                          /\ CommitStateUpdate(msg)
                                       \/ /\ msg.snapshotVersion < versionToCompare
                                          /\ AbortStateUpdate(msg)    
                                    
Init == /\ checkpoint = 0 \* 0 means no check point recorded.
        /\ nodeState = [snapshotVersion |-> 0, leastSnapshotVersion |-> 0, leastInstalledVersion |-> 0, valueMap |->  <<>>, lastProcessedVersion |-> 0]
        /\ abcast = <<>>
        /\ stateSnapshots = <<>>
        /\ runCounter = 1
        
        
Next == \E k \in Keys: \/ NodeInsertMsg(k)
                       \/ NodeUpdateMsg(k)
                       \/ NodeUpdateCheckpoint
                       \/ NodeReset
                       \/ NodeRecvMessage

\* This check of checking the equality between value maps works for single Key. 
\* As for any snapshot in multiple runs, we can only gurrantee if the key exist in both value maps then state is same but there can still be some keys missing.
\* As they are not hydrated yet.
ConsistentBetweenRuns == \A i, j \in DOMAIN stateSnapshots: \/ /\ i # j
                                                               /\ stateSnapshots[i].runCounter # stateSnapshots[j].runCounter
                                                               /\ stateSnapshots[i].snapshotVersion = stateSnapshots[j].snapshotVersion
                                                               /\ \A k1 \in DOMAIN stateSnapshots[i].valueMap: \A k2 \in DOMAIN stateSnapshots[j].valueMap: \/ /\ stateSnapshots[i].valueMap[k1].key = stateSnapshots[j].valueMap[k2].key
                                                                                                                                                               /\ stateSnapshots[i].valueMap[k1].value = stateSnapshots[j].valueMap[k2].value
                                                                                                                                                            \/ stateSnapshots[i].valueMap[k1].key # stateSnapshots[j].valueMap[k2].key
                                                            \/ /\ i # j
                                                               /\ stateSnapshots[i].runCounter = stateSnapshots[j].runCounter
                                                            \/ /\ i # j
                                                               /\ stateSnapshots[i].runCounter # stateSnapshots[j].runCounter
                                                               /\ stateSnapshots[i].snapshotVersion # stateSnapshots[j].snapshotVersion
                                                            \/ i = j  



Spec == Init /\ [][Next]_<<nodeState, abcast, checkpoint, runCounter, stateSnapshots>>

THEOREM Invariance == Spec => [](TypeOK /\ ConsistentBetweenRuns /\ DataInvariant)


\* Buggy implementation to check if model can catch this.
\* Update checkpoint based on leastInstalledVersion instead of leastSnapshotVersion


BuggyNodeUpdateCheckpoint ==  /\ checkpoint < nodeState.leastInstalledVersion
                              /\ checkpoint' = nodeState.leastInstalledVersion
                              /\ UNCHANGED <<nodeState, abcast, runCounter, stateSnapshots>>
                              
BuggyNext == \E k \in Keys: \/ NodeInsertMsg(k)
                            \/ NodeUpdateMsg(k)
                            \/ BuggyNodeUpdateCheckpoint
                            \/ NodeReset
                            \/ NodeRecvMessage

BuggySpec == Init /\ [][BuggyNext]_<<nodeState, abcast, checkpoint, runCounter, stateSnapshots>>

\* End of Buggy implementation.


\* State Constraints to bount the space exploration
\*/\ \A index \in DOMAIN nodeState.valueMap: nodeState.valueMap[index].value < 10000
\*/\ runCounter < 1000
\*/\ Len(abcast) < 100000
\*/\ checkpoint < 100000


\* This did not yield a result after 1 hour 20 mins run. 944,013,418 states found.396,167,014 distinct states
\*/\ \A index \in DOMAIN nodeState.valueMap: nodeState.valueMap[index].value < 100
\*/\ runCounter < 100
\*/\ Len(abcast) < 1000
\*/\ checkpoint < 1000

=============================================================================
\* Modification History
\* Last modified Thu Dec 19 07:23:52 IST 2024 by anisha
\* Created Fri Dec 13 19:20:28 AEDT 2024 by anisha
