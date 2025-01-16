------------------------- MODULE zerokv_singlenode -------------------------

EXTENDS Integers, Sequences
    
\*
\* Keys are set of keys that will take part in transactions.
\* Nodes define the set of total number of participating nodes. Each node can add a data message to abcast to update one of the keys or it can add a message to record a checkpoint. 
\* Example: 
\* Nodes = {"n1", "n2"}
\* Keys = {"k1", "k2"}
\*
CONSTANT Keys, Nodes

\*
\* abcast is a append only sequence of Messages. 
\* checkpoint is global checkpoint that can be read by all nodes. This is updated after checkpoint is certified. Also used at the time of nodeResetOperation to mimic restart of the node.
\* nodeMap is map implementation to store key value pairs along with snapshotVersion. It's in form of [Keys -> Data].
\* nodeLastProcessedVersion is there to keep track of last processed message. This will be updated in both commit and abort cases.
\* nodeCheckpoint stores the local checkpoint for a node. This gets updated at the start of node restoring from global checkpoint and when CHECKPOINT_INTENT message is committed.
\*
\*
VARIABLES checkpoint, abcast, nodeMap, nodeLastProcessedVersion, nodeCheckpoint


\*
\* Two types of message operations are supported, DATA or CHECKPOINT_INTENT.
\*
Messages == [operation: {"DATA"}, key: Keys, value: Nat, version: Nat, snapshotVersion: Nat \union {0}] \union [operation: {"CHECKPOINT_INTENT"}, version: Nat, snapshotVersion: Nat]

\*
\* Value field of key-value data store nodeMap. 
\* 0 is allowed in snapshotVersion to support addition of message in empty state. 
\*
Data == [value: Nat, version: Nat, snapshotVersion: Nat \union {0}]


\*
\* "INVALID" is a reserved value in keys which is used to handle the case of no matching keys. This is used in NodeUpdateCheckpoint operation where we are trying to find minimumSnapshotVersion but no record is yet replicated. i.e. all records in a map have version 0.
\* In our data set, we always initiate the nodeMap with version: 0. But all keys are always present in a map.
\*
ASSUME \A k \in Keys: k # "INVALID" \* Reserved

      
Init == /\ checkpoint = 0 \* 0 means no check point recorded.
        /\ abcast = <<>>
        /\ nodeMap = [n \in Nodes |-> [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]]]
        /\ nodeLastProcessedVersion = [n \in Nodes |-> 0]
        /\ nodeCheckpoint = [n \in Nodes |-> 0]

\*
\* MaxInstalledVersionKey is used to calculate the snapshot version that needs to be submitted at the time of adding key for certification in abcast. 
\*        
MaxInstalledVersionKey(n) == CHOOSE k1 \in DOMAIN nodeMap[n]: \A k2 \in DOMAIN nodeMap[n]: nodeMap[n][k1].version >= nodeMap[n][k2].version
        
\*
\* MinimumSnapshotVersionKey returns the key of record which has minimum snapshotVersion or INVALID if every record has version 0.
\* Accepts the argument of nodemap of particular node.
\*
MinimumSnapshotVersionKey(localNodeMap) ==  IF \E k1, k2 \in DOMAIN localNodeMap: localNodeMap[k1].version # 0 /\ localNodeMap[k2].version # 0 /\ k1 # k2 \* Atleast 2 valid entries are there.
                                            THEN CHOOSE k1 \in DOMAIN localNodeMap: \A k2 \in DOMAIN localNodeMap: /\ localNodeMap[k2].version # 0
                                                                                                                   /\ localNodeMap[k1].version # 0  
                                                                                                                   /\ localNodeMap[k1].snapshotVersion <= localNodeMap[k2].snapshotVersion       
                                            ELSE IF \E k \in DOMAIN localNodeMap: localNodeMap[k].version # 0 
                                                 THEN CHOOSE k \in DOMAIN localNodeMap: localNodeMap[k].version # 0
                                                 ELSE "INVALID"

                      
\*
\* AbortStateUpdate: Ignores the state update. We only update the nodeLastProcessedVersion for node n. This is required to make progress and to mimic next() function in iterator.
\*
AbortStateUpdate(n, msg) == /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = msg.version]
                            /\ UNCHANGED <<abcast, checkpoint, nodeMap, nodeCheckpoint>>

\*
\* CommitStateUpdate: Updates the nodeLastProcessedVersion and nodeMap for node n with new state from message for given key in message msg.
\* nodeLastProcessedVersion is updated to make progress, to make sure on next NodeRecvMessage,  same message is not read again.
\*
CommitStateUpdate(n, msg) ==  /\ LET value == [value |-> msg.value, snapshotVersion |-> msg.snapshotVersion, version |-> msg.version]
                                 IN /\ nodeMap' = [nodeMap EXCEPT ![n][msg.key] = value] 
                                    /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = msg.version]                        
                              /\ UNCHANGED <<abcast, checkpoint, nodeCheckpoint>>

\*
\* NodeHandleDataMessage:If data does not exist in local, we compare nodeCheckpoint with msg.snapshotVersion. This is to make sure once checkpoint is committed, no transaction below that checkpoint is committed by any node.
\* if data does exist in local we compare the local record version to msg.snapshotVersion to check for concurrent updates.
\* Concurrent Updates: When node tries to update the record before observing all the previous updates.
\* In case all previous updates has been observed by node,  msg.snapshotVersion will be greater than installed version or checkpoint in case of record is not present.
\*
NodeHandleDataMessage(n, msg) == LET versionToCompare == IF nodeMap[n][msg.key].version = 0 THEN nodeCheckpoint[n] ELSE nodeMap[n][msg.key].version
                                 IN \/ /\ versionToCompare > msg.snapshotVersion \* Abort: No installation of valueMap. Only update lastProcessedVersion
                                       /\ AbortStateUpdate(n, msg)
                                    \/ /\ versionToCompare <= msg.snapshotVersion
                                       /\ CommitStateUpdate(n, msg)

\*
\* NodeCommitCheckpoint: In case of Commit operation for checkpoint, Both global and local checkpoint of a node is updated.
\* Again, to make progress nodeLastProcessedVersion is updated for given node n.
\*

NodeCommitCheckpoint(n, msg) == /\ checkpoint' = msg.snapshotVersion
                                /\ nodeCheckpoint' = [nodeCheckpoint EXCEPT ![n]=  msg.snapshotVersion]
                                /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = msg.version]                            
                                /\ UNCHANGED <<abcast, nodeMap>>
                                  
\*
\* NodeCommitLocalCheckpoint: In case a particular node is behind in reading message, it is possible that global checkpoint is moved further.
\* In this case, only local checkpoint will be committed, This is required to make sure every node is always at same state for a particular offset of abcast.
\*
NodeCommitLocalCheckpoint(n, msg) == /\ nodeCheckpoint' = [nodeCheckpoint EXCEPT ![n] = msg.snapshotVersion]
                                     /\ nodeLastProcessedVersion' = [nodeLastProcessedVersion EXCEPT ![n] = msg.version]                            
                                     /\ UNCHANGED <<abcast, checkpoint, nodeMap>>                                  
                                       

\*
\* NodeHandleCheckpointIntent: In case some record has been committed with snapshotVersion less than snapshotVersion submitted in CHECKPOINT_INTENT message, checkpoint will be aborted.
\* If submitted snapshotVersion is greater than global checkpoint, then checkpoint can be committed locally and globally.
\* If global checkpoint is same or greater than intended checkpoint, only local node checkpoint is updated.
\*
NodeHandleCheckpointIntent(n, msg) ==  IF \E index \in DOMAIN abcast: abcast[index].snapshotVersion < msg.snapshotVersion
                                       THEN AbortStateUpdate(n, msg)
                                       ELSE IF checkpoint < msg.snapshotVersion 
                                            THEN NodeCommitCheckpoint(n, msg)
                                            ELSE NodeCommitLocalCheckpoint(n, msg) 
                                              

                                         
\*
\* Reads the next message and call relevant function based on message type.
\*
NodeRecvMessage(n) == /\ Len(abcast) > 0 \* Atleast one message exist in abcast                
                      /\ nodeLastProcessedVersion[n] < Len(abcast) \* Atleast one New message exist to receive.
                      /\ LET NextIndexToRead == nodeLastProcessedVersion[n] + 1
                             msg == abcast[NextIndexToRead]
                         IN \/ /\ msg.operation = "DATA"
                               /\ NodeHandleDataMessage(n, msg)
                            \/ /\ msg.operation = "CHECKPOINT_INTENT"
                               /\ NodeHandleCheckpointIntent(n, msg)
                               
                               
\*
\* Helper operation to append a message to abcast. Check Messages to know the details about type of messages that can be added to abcast.
\*
SendToAbcast(m) == abcast' = abcast \o <<m>>                               
                        
\*
\* Submits a CHECKPOINT_INTENT message to abcast only when at least one message is replicated and global checkpoint is less than intended snapshotVersion.
\*
NodeUpdateCheckpoint(n) ==  /\ LET key == MinimumSnapshotVersionKey(nodeMap[n]) 
                               IN /\ key # "INVALID"
                                  /\ checkpoint < nodeMap[n][key].snapshotVersion
                                  /\ SendToAbcast([operation |-> "CHECKPOINT_INTENT",
                                       version |-> Len(abcast) + 1,
                                       snapshotVersion |-> nodeMap[n][key].snapshotVersion])
                            /\ UNCHANGED <<nodeLastProcessedVersion, nodeMap, nodeCheckpoint, checkpoint>>
                           
                            
\*
\* NodeAddMsg: Operator to send add data message for node n. 
\* snapShotVersion is calculated based on local nodeMap for node n.
\* version will be index of abcast where message will be appended.
\* value is updated by adding 1 to local value. Initial Value of all records is 0.
\*
NodeAddMsg(n, key) == /\ SendToAbcast([key |-> key,
                                       value |-> nodeMap[n][key].value + 1,
                                       version |-> Len(abcast) + 1,
                                       snapshotVersion |-> nodeMap[n][MaxInstalledVersionKey(n)].version,
                                       operation |-> "DATA"])
                                                
                      /\ UNCHANGED <<nodeMap, checkpoint, nodeLastProcessedVersion, nodeCheckpoint>>        


Next == \E n \in Nodes: \/ NodeRecvMessage(n)
                        \/ NodeUpdateCheckpoint(n)
                        \/ \E key \in Keys: \/ NodeAddMsg(n, key)
        
TypeInvariant == /\ \A i \in DOMAIN abcast: {abcast[i]} \subseteq Messages
                 /\ checkpoint \in Nat \union {0}
                 /\ nodeMap \in [Nodes -> [Keys -> Data]]
                 /\ nodeLastProcessedVersion \in [Nodes -> Nat]
                 /\ nodeCheckpoint \in [Nodes -> Nat]
                 
 
CheckpointInvariant == /\ checkpoint <= Len(abcast)
                       /\ \A n \in Nodes: nodeCheckpoint[n] <= checkpoint 
           
                       
RECURSIVE ReplicateFromOffset(_, _, _)

\*
\* Recursive function to build a state in localNodeMap, reading one message from abcast one at a time on particular offset.
\* localCheckpoint defines the starting point of state replication, In case checkpoint exist, it will start replication for selected checkpoint.
\*
ReplicateFromOffset(localNodeMap, offset, localCheckpoint) == IF offset <= Len(abcast)
                                                              THEN LET msg == abcast[offset]
                                                                   IN IF msg.operation = "DATA"
                                                                      THEN LET versionToCompare == IF localNodeMap[msg.key].version = 0 THEN localCheckpoint ELSE localNodeMap[msg.key].version
                                                                           IN IF versionToCompare > msg.snapshotVersion \* Abort: No installation of state. Only update lastProcessedVersion
                                                                              THEN ReplicateFromOffset(localNodeMap, offset + 1, localCheckpoint)
                                                                              ELSE LET value == [value |-> msg.value, snapshotVersion |-> msg.snapshotVersion, version |-> msg.version]
                                                                                   IN ReplicateFromOffset([localNodeMap EXCEPT ![msg.key] = value], offset + 1, localCheckpoint)
                                                                      ELSE IF \E index \in DOMAIN abcast: abcast[index].snapshotVersion < msg.snapshotVersion \* Check if there is any other update between intended checkpoint and version of CHECKPOINT_INTENT message.
                                                                           THEN ReplicateFromOffset(localNodeMap, offset + 1, localCheckpoint) \* Abort localcheckpoint update
                                                                           ELSE ReplicateFromOffset(localNodeMap, offset + 1, msg.snapshotVersion) \* Commit localcheckpoint update
                                                              ELSE localNodeMap
\*
\* For any selected checlkpoint, node state should be equivalent to as if it is replicated from start without checkpoint.
\*
ConsistencyInvariant ==  \/ /\ checkpoint # 0
                            /\ LET checkpointMap == [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]]
                                   initialMap == [k \in Keys |-> [value |-> 0, version |-> 0, snapshotVersion |-> 0]] 
                               IN ReplicateFromOffset(checkpointMap, checkpoint + 1, checkpoint) = ReplicateFromOffset(initialMap, 1, 0)
                         \/ checkpoint = 0
Spec == Init /\ [][Next]_<<nodeMap, abcast, checkpoint, nodeLastProcessedVersion, nodeCheckpoint>>

THEOREM Invariance == Spec => [](TypeInvariant /\ ConsistencyInvariant /\ CheckpointInvariant)


\* State Constraints to bound the space exploration for 2 nodes and 2 keys
\*/\ \A n \in Nodes: \A key \in DOMAIN nodeMap[n]: /\ nodeMap[n][key].value < 5
\*                                                 /\ runCounter[n] < 3
\*/\ Len(abcast) < 8
\*/\ checkpoint < 6


=============================================================================
\* Modification History
\* Last modified Fri Jan 17 00:07:36 AEDT 2025 by anisha
\* Created Fri Dec 13 19:20:28 AEDT 2024 by anisha
