------------------------- MODULE zerokv_singlenode -------------------------

EXTENDS Integers, Sequences
    
CONSTANT Keys, Nodes


VARIABLES checkpoint, abcast, runCounter, nodeMap, nodeSnapshotVersion, nodeLastProcessedVersion, nodeCheckpoint
\* message has fields: key, value, version, snapshotVersion 
Messages == [operation: {"DATA"}, key: Keys, value: Nat, version: Nat, snapshotVersion: Nat \union {0}] \union [operation: {"CHECKPOINT_INTENT"}, version: Nat, snapshotVersion: Nat]

\* Data to be stored in each node. Check TypeOK for details.
\* Data is stored in the form of sequence againt valueMap field. TODO: Store in Record format
Data == [value: Nat, version: Nat, snapshotVersion: Nat \union {0}]

ASSUME \A k \in Keys: k # "INVALID" \* Reserved

DataSet == [Keys -> Data]
      
Init == /\ checkpoint = 0 \* 0 means no check point recorded.
        /\ abcast = <<>>
        /\ runCounter = [n \in Nodes |-> 1]
        /\ nodeMap = [n \in Nodes |-> [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]]]
        /\ nodeSnapshotVersion = [n \in Nodes |-> 0]
        /\ nodeLastProcessedVersion = [n \in Nodes |-> 0]
        /\ nodeCheckpoint = [n \in Nodes |-> 0]
        
\* Update Checkpoint based on leastSnapshotVersion and leastInstalledVersion
\* Update: We are just checking leastSnapshotVersion as snapshot version submitted with a record will always be less than the version itself.

MinimumSnapshotVersionKey(n) ==  IF \E k1, k2 \in DOMAIN nodeMap[n]: nodeMap[n][k1].version # 0 /\ nodeMap[n][k2].version # 0 /\ k1 # k2 \* Atleast 2 valid entries are there.
                                 THEN CHOOSE k1 \in DOMAIN nodeMap[n]: \A k2 \in DOMAIN nodeMap[n]: /\ nodeMap[n][k2].version # 0
                                                                                                    /\ nodeMap[n][k1].version # 0  
                                                                                                    /\ nodeMap[n][k1].snapshotVersion <= nodeMap[n][k2].snapshotVersion       
                                 ELSE IF \E k \in DOMAIN nodeMap[n]: nodeMap[n][k].version # 0 
                                      THEN CHOOSE k \in DOMAIN nodeMap[n]: nodeMap[n][k].version # 0
                                      ELSE "INVALID"
SendToAbcast(m) == abcast' = abcast \o <<m>>

NodeUpdateCheckpoint(n) ==  /\ LET key == MinimumSnapshotVersionKey(n) 
                               IN /\ key # "INVALID"
                                  /\ checkpoint < nodeMap[n][key].snapshotVersion
                                  /\ SendToAbcast([operation |-> "CHECKPOINT_INTENT",
                                       version |-> Len(abcast) + 1,
                                       snapshotVersion |-> nodeMap[n][key].snapshotVersion])
                            /\ UNCHANGED <<runCounter, nodeLastProcessedVersion, nodeSnapshotVersion, nodeMap, nodeCheckpoint, checkpoint>>  

NodeReset(n) == /\ nodeMap' = [nodeMap EXCEPT ![n] = [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]]]
                /\ runCounter' = [runCounter EXCEPT ![n] = runCounter[n] + 1]
                /\ nodeSnapshotVersion' = [nodeSnapshotVersion EXCEPT ![n] = checkpoint]
                /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = checkpoint]
                /\ nodeCheckpoint' = [nodeCheckpoint EXCEPT ![n] = checkpoint]
                /\ UNCHANGED <<abcast, checkpoint>>
             


\* InsertRecort: Operator to publish to abcast after local checks. We check locally if key does not exist before proceeding with insert operation. TODO: We will remove the local checks to see if certification still pass.

NodeAddMsg(n, key) == /\ SendToAbcast([key |-> key,
                                       value |-> nodeMap[n][key].value + 1,
                                       version |-> Len(abcast) + 1,
                                       snapshotVersion |-> nodeSnapshotVersion[n],
                                       operation |-> "DATA"])
                                                
                      /\ UNCHANGED <<nodeMap, checkpoint, runCounter, nodeSnapshotVersion, nodeLastProcessedVersion, nodeCheckpoint>>
                      
\* State update Helper funtion in case of Abort transaction. This is used  in  NodeRecvMessage Operator.
\* Why do we update snapshot version in case of Abort?
\* This is required to make progress now. As We are getting message after lastProcessedState                                              
AbortStateUpdate(n, msg) == /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = msg.version]
                            /\ UNCHANGED <<abcast, checkpoint, runCounter, nodeMap, nodeSnapshotVersion, nodeCheckpoint>>

\* State update Helper funtion in case of Commit transaction. This is used  in  NodeRecvMessage Operator. 
CommitStateUpdate(n, msg) ==  /\ LET value == [value |-> msg.value, snapshotVersion |-> msg.snapshotVersion, version |-> msg.version]
                                 IN /\ nodeMap' = [nodeMap EXCEPT ![n][msg.key] = value] 
                                    /\ nodeSnapshotVersion' = [nodeSnapshotVersion EXCEPT ![n] = msg.version]
                                    /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = msg.version]                        
                              /\ UNCHANGED <<abcast, checkpoint, runCounter, nodeCheckpoint>>

NodeHandleDataMessage(n, msg) == LET versionToCompare == IF nodeMap[n][msg.key].version = 0 THEN nodeCheckpoint[n] ELSE nodeMap[n][msg.key].version
                                 IN \/ /\ versionToCompare > msg.snapshotVersion \* Abort: No installation of valueMap. Only update lastProcessedVersion
                                       /\ AbortStateUpdate(n, msg)
                                    \/ /\ versionToCompare <= msg.snapshotVersion
                                       /\ CommitStateUpdate(n, msg)

NodeCommitCheckpoint(n, msg) == /\ checkpoint' = msg.snapshotVersion
                                /\ nodeCheckpoint' = [nodeCheckpoint EXCEPT ![n]=  msg.snapshotVersion]
                                /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = msg.version]                            
                                /\ UNCHANGED <<abcast, checkpoint, runCounter, nodeMap>>
                                  
NodeCommitLocalCheckpoint(n, msg) == /\ nodeCheckpoint' = [nodeCheckpoint EXCEPT ![n] = msg.snapshotVersion]
                                     /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = msg.version]                            
                                     /\ UNCHANGED <<abcast, checkpoint, runCounter, nodeCheckpoint, nodeMap>>                                  
                                       
NodeHandleCheckpointIntent(n, msg) == LET key == MinimumSnapshotVersionKey(n)
                                      IN IF nodeMap[n][key].snapshotVersion < msg.version
                                         THEN AbortStateUpdate(n, msg)
                                         ELSE IF nodeCheckpoint < nodeMap[n][key].snapshotVersion 
                                              THEN NodeCommitCheckpoint(n, msg)
                                              ELSE NodeCommitLocalCheckpoint(n, msg) 
                                         

NodeRecvMessage(n) == /\ Len(abcast) > 0 \* Atleast one message exist in abcast                
                      /\ nodeLastProcessedVersion[n] < Len(abcast) \* Atleast one New message exist to receive.
                      /\ LET NextIndexToRead == nodeLastProcessedVersion[n] + 1
                             msg == abcast[NextIndexToRead]
                         IN \/ /\ msg.operation = "DATA"
                               /\ NodeHandleDataMessage(n, msg)
                            \/ /\ msg.operation = "CHECKPOINT_INTENT"
                               /\ NodeHandleCheckpointIntent(n, msg)
                               


Next == \E n \in Nodes: \/ NodeReset(n)
                        \/ NodeRecvMessage(n)
                        \/ NodeUpdateCheckpoint(n)
                        \/ \E key \in Keys: \/ NodeAddMsg(n, key)
        
TypeInvariant == /\ \A i \in DOMAIN abcast: {abcast[i]} \subseteq Messages
                 /\ checkpoint \in Nat \union {0}
                 /\ runCounter \in [Nodes -> Nat]
                 /\ nodeMap \in [Nodes -> [Keys -> Data]]
                 /\ nodeSnapshotVersion \in [Nodes -> Nat]
                 /\ nodeLastProcessedVersion \in [Nodes -> Nat]
                 /\ nodeCheckpoint \in [Nodes -> Nat]
                 
 
CheckpointInvariant == /\ checkpoint <= Len(abcast)
                       /\ \A n \in Nodes: nodeCheckpoint[n] <= checkpoint 
           
                       
RECURSIVE ReplicateFromOffset(_, _, _)

ReplicateFromOffset(localNodeMap, offset, localCheckpoint) == IF offset <= Len(abcast)
                                                              THEN LET msg == abcast[offset]
                                                                       versionToCompare == IF localNodeMap[msg.key].version = 0 THEN localCheckpoint ELSE localNodeMap[msg.key].version
                                                                   IN IF versionToCompare > msg.snapshotVersion \* Abort: No installation of valueMap. Only update lastProcessedVersion
                                                                      THEN ReplicateFromOffset(localNodeMap, offset + 1, localCheckpoint)
                                                                      ELSE LET value == [value |-> msg.value, snapshotVersion |-> msg.snapshotVersion, version |-> msg.version]
                                                                           IN ReplicateFromOffset([localNodeMap EXCEPT ![msg.key] = value], offset + 1, localCheckpoint)
                                                              ELSE localNodeMap
             
ConsistencyInvariant ==  \/ /\ checkpoint # 0
                            /\ LET checkpointMap == [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]]
                                   initialMap == [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]] 
                               IN ReplicateFromOffset(checkpointMap, checkpoint + 1, checkpoint) = ReplicateFromOffset(initialMap, 1, 0)
                         \/ checkpoint = 0
Spec == Init /\ [][Next]_<<nodeMap, abcast, checkpoint, runCounter, nodeLastProcessedVersion, nodeSnapshotVersion, nodeCheckpoint>>

THEOREM Invariance == Spec => [](TypeInvariant /\ ConsistencyInvariant /\ CheckpointInvariant)


\* Buggy implementation to check if model can catch this.
\* Update checkpoint based on leastInstalledVersion instead of leastSnapshotVersion

\*MinimumVersionKey ==  CHOOSE k1 \in DOMAIN nodeMap: \A k2 \in DOMAIN nodeMap: nodeMap[k1].version < nodeMap[k2].version
\*
\*BuggyNodeUpdateCheckpoint ==  /\ LET key == MinimumVersionKey 
\*                                 IN /\ checkpoint < nodeMap[key].version
\*                                    /\ checkpoint' = nodeMap[key].version
\*                              /\ UNCHANGED <<abcast, runCounter, nodeLastProcessedVersion, nodeSnapshotVersion, nodeMap>> 
\*                              
\*BuggyNext == \/ NodeReset
\*             \/ NodeRecvMessage
\*             \/ NodeUpdateCheckpoint
\*             \/ \E key \in Keys: \/ NodeAddMsg(key)
\*
\*BuggySpec == Init /\ [][BuggyNext]_<<nodeMap, abcast, checkpoint, runCounter, nodeLastProcessedVersion, nodeSnapshotVersion>>

\* abcast = k1(0), k2(1), k3(0)
\* add k1 -> recv -> add k2 -> recv -> add k1 checkpoint -> add -> reset -> recv  
\* In straight forward run all these should be allowed. However in the case where checkpoint is created at index 2. 
\* by min version formula, it should be 2,
\* by min snapshot formula it should be 1.
\* in both cases tx at index 3 will fail but for initial run it will pass. Both formulas are wrong. 
\* to prove above scenario: min 2 runs, min checkpoint of 1 required. len(abcast) of 3 required.
\* Above is valid scenario but atleast 2 nodes are required to prove.
\* Why? -> In single node, if we are recieiving, snapshot is always moving, Reset starts the node at checkpoint. There is no way to send a message on older snapshot and checkpointing at higher using single node.
\* State Constraints to bound the space exploration for 2 nodes and 2 keys
\*/\ \A n \in Nodes: \A key \in DOMAIN nodeMap[n]: /\ nodeMap[n][key].value < 4
\*                                                 /\ runCounter[n] < 4
\*/\ Len(abcast) < 6
\*/\ checkpoint < 6


=============================================================================
\* Modification History
\* Last modified Sun Jan 12 01:10:38 AEDT 2025 by anisha
\* Created Fri Dec 13 19:20:28 AEDT 2024 by anisha
