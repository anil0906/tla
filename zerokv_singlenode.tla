------------------------- MODULE zerokv_singlenode -------------------------

EXTENDS Integers, Sequences
    
CONSTANT Keys


VARIABLES checkpoint, abcast, runCounter, nodeMap, nodeSnapshotVersion, nodeLastProcessedVersion
\* message has fields: key, value, version, snapshotVersion 
Messages == [key: Keys, value: Nat, version: Nat, snapshotVersion: Nat \union {0}]

\* Data to be stored in each node. Check TypeOK for details.
\* Data is stored in the form of sequence againt valueMap field. TODO: Store in Record format
Data == [value: Nat, version: Nat, snapshotVersion: Nat \union {0}]

ASSUME \A k \in Keys: k # "INVALID" \* Reserved

DataSet == [Keys -> Data]
      
Init == /\ checkpoint = 0 \* 0 means no check point recorded.
        /\ abcast = <<>>
        /\ runCounter = 1
        /\ nodeMap = [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]]
        /\ nodeSnapshotVersion = 0
        /\ nodeLastProcessedVersion = 0
        
\* Update Checkpoint based on leastSnapshotVersion and leastInstalledVersion
\* Update: We are just checking leastSnapshotVersion as snapshot version submitted with a record will always be less than the version itself.

MinimumSnapshotVersionKey ==  IF \E k1, k2 \in DOMAIN nodeMap: nodeMap[k1].version # 0 /\ nodeMap[k2].version # 0 /\ k1 # k2 \* Atleast 2 valid entries are there.
                              THEN CHOOSE k1 \in DOMAIN nodeMap: \A k2 \in DOMAIN nodeMap: /\ nodeMap[k2].version # 0
                                                                                           /\ nodeMap[k1].version # 0  
                                                                                           /\ nodeMap[k1].snapshotVersion <= nodeMap[k2].snapshotVersion       
                              ELSE IF \E k \in DOMAIN nodeMap: nodeMap[k].version # 0 
                                   THEN CHOOSE k \in DOMAIN nodeMap: nodeMap[k].version # 0
                                   ELSE "INVALID"

NodeUpdateCheckpoint ==  /\ LET key == MinimumSnapshotVersionKey 
                            IN /\ key # "INVALID"
                               /\ checkpoint < nodeMap[key].snapshotVersion
                               /\ checkpoint' = nodeMap[key].snapshotVersion
                         /\ UNCHANGED <<abcast, runCounter, nodeLastProcessedVersion, nodeSnapshotVersion, nodeMap>>  

NodeReset == /\ nodeMap' = [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]]
             /\ runCounter' = runCounter + 1
             /\ nodeSnapshotVersion' = checkpoint
             /\ nodeLastProcessedVersion' = checkpoint
             /\ UNCHANGED <<abcast, checkpoint>>
             
SendToAbcast(m) == abcast' = abcast \o <<m>>

\* InsertRecort: Operator to publish to abcast after local checks. We check locally if key does not exist before proceeding with insert operation. TODO: We will remove the local checks to see if certification still pass.

NodeAddMsg(key) == /\ SendToAbcast([key |-> key,
                                       value |-> nodeMap[key].value + 1,
                                       version |-> Len(abcast) + 1,
                                       snapshotVersion |-> nodeSnapshotVersion])
                                                
                   /\ UNCHANGED <<nodeMap, checkpoint, runCounter, nodeSnapshotVersion, nodeLastProcessedVersion>>
                      
\* State update Helper funtion in case of Abort transaction. This is used  in  NodeRecvMessage Operator.
\* Why do we update snapshot version in case of Abort?
\* This is required to make progress now. As We are getting message after lastProcessedState                                              
AbortStateUpdate(msg) == /\ nodeLastProcessedVersion' = msg.version
                         /\ UNCHANGED <<abcast, checkpoint, runCounter, nodeMap, nodeSnapshotVersion>>

\* State update Helper funtion in case of Commit transaction. This is used  in  NodeRecvMessage Operator. 
CommitStateUpdate(msg) ==  /\ LET value == [value |-> msg.value, snapshotVersion |-> msg.snapshotVersion, version |-> msg.version]
                                  existingValueMap == nodeMap
                               IN /\ nodeMap' = [nodeMap EXCEPT ![msg.key] = value] 
                                  /\ nodeSnapshotVersion' = msg.version
                                  /\ nodeLastProcessedVersion' = msg.version                        
                           /\ UNCHANGED <<abcast, checkpoint, runCounter>>


NodeRecvMessage == /\ Len(abcast) > 0 \* Atleast one message exist in abcast                
                   /\ nodeLastProcessedVersion < Len(abcast) \* Atleast one New message exist to receive.
                   /\ LET NextIndexToRead == nodeLastProcessedVersion + 1
                          msg == abcast[NextIndexToRead]
                          versionToCompare == IF nodeMap[msg.key].version = 0 THEN checkpoint ELSE nodeMap[msg.key].version
                      IN \/ /\ versionToCompare > msg.snapshotVersion \* Abort: No installation of valueMap. Only update lastProcessedVersion
                            /\ AbortStateUpdate(msg)
                         \/ /\ versionToCompare <= msg.snapshotVersion
                            /\ CommitStateUpdate(msg) 

Next == \/ NodeReset
        \/ NodeRecvMessage
        \/ NodeUpdateCheckpoint
        \/ \E key \in Keys: \/ NodeAddMsg(key)
        
TypeInvariant == /\ \A i \in DOMAIN abcast: {abcast[i]} \subseteq Messages
                 /\ checkpoint \in Nat \union {0}
                 /\ runCounter \in Nat
                 /\ nodeMap \in [Keys -> Data]
                 /\ nodeSnapshotVersion \in Nat
                 /\ nodeLastProcessedVersion \in Nat
 
CheckpointInvariant == /\ checkpoint <= Len(abcast)
                       /\ LET key == MinimumSnapshotVersionKey
                          IN  \/ key = "INVALID"
                              \/ /\ key # "INVALID" 
                                 /\ checkpoint <= nodeMap[key].snapshotVersion
                       
                       
RECURSIVE ReplicateFromOffset(_, _, _)

ReplicateFromOffset(localNodeMap, offset, localCheckpoint) == IF offset <= Len(abcast)
                                                              THEN LET msg == abcast[offset]
                                                                       versionToCompare == IF localNodeMap[msg.key].version = 0 THEN localCheckpoint ELSE localNodeMap[msg.key].version
                                                                   IN IF versionToCompare > msg.snapshotVersion \* Abort: No installation of valueMap. Only update lastProcessedVersion
                                                                      THEN ReplicateFromOffset(localNodeMap, offset + 1, localCheckpoint)
                                                                      ELSE ReplicateFromOffset(localNodeMap, offset + 1, localCheckpoint)
                                                              ELSE nodeMap
             
ConsistencyInvariant ==  \/ /\ checkpoint # 0
                            /\ LET checkpointMap == [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]]
                                   initialMap == [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]] 
                               IN ReplicateFromOffset(checkpointMap, checkpoint + 1, checkpoint) = ReplicateFromOffset(initialMap, 1, 0)
                         \/ checkpoint = 0
Spec == Init /\ [][Next]_<<nodeMap, abcast, checkpoint, runCounter, nodeLastProcessedVersion, nodeSnapshotVersion>>

THEOREM Invariance == Spec => [](TypeInvariant /\ ConsistencyInvariant /\ CheckpointInvariant)


\* Buggy implementation to check if model can catch this.
\* Update checkpoint based on leastInstalledVersion instead of leastSnapshotVersion

MinimumVersionKey ==  CHOOSE k1 \in DOMAIN nodeMap: \A k2 \in DOMAIN nodeMap: nodeMap[k1].version < nodeMap[k2].version

BuggyNodeUpdateCheckpoint ==  /\ LET key == MinimumVersionKey 
                                 IN /\ checkpoint < nodeMap[key].version
                                    /\ checkpoint' = nodeMap[key].version
                              /\ UNCHANGED <<abcast, runCounter, nodeLastProcessedVersion, nodeSnapshotVersion, nodeMap>> 
                              
BuggyNext == \/ NodeReset
             \/ NodeRecvMessage
             \/ NodeUpdateCheckpoint
             \/ \E key \in Keys: \/ NodeAddMsg(key)

BuggySpec == Init /\ [][BuggyNext]_<<nodeMap, abcast, checkpoint, runCounter, nodeLastProcessedVersion, nodeSnapshotVersion>>

\* abcast = k1(0), k2(1), k3(0)
\* add k1 -> recv -> add k2 -> recv -> add k1 checkpoint -> add -> reset -> recv  
\* In straight forward run all these should be allowed. However in the case where checkpoint is created at index 2. 
\* by min version formula, it should be 2,
\* by min snapshot formula it should be 1.
\* in both cases tx at index 3 will fail but for initial run it will pass. Both formulas are wrong. 
\* to prove above scenario: min 2 runs, min checkpoint of 1 required. len(abcast) of 3 required.
\* Above is valid scenario but atleast 2 nodes are required to prove.
\* Why? -> In single node, if we are recieiving, snapshot is always moving, Reset starts the node at checkpoint. There is no way to send a message on older snapshot and checkpointing at higher using single node.
\* State Constraints to bound the space exploration
\*/\ \A key \in DOMAIN nodeMap: nodeMap[key].value < 3
\*/\ runCounter < 3
\*/\ Len(abcast) < 4
\*/\ checkpoint < 4


=============================================================================
\* Modification History
\* Last modified Sat Jan 11 01:21:11 AEDT 2025 by anisha
\* Created Fri Dec 13 19:20:28 AEDT 2024 by anisha
