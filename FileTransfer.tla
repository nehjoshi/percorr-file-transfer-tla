--------------------------- MODULE FileTransfer ---------------------------


VARIABLES
    lState,         
    fState,         
    restartHandled, 
    fResult,        \* result the Follower will put in its BlobReply
    fileOnDisk,     \* TRUE once the Follower's disk durably holds the file
    msgs            \* messages in the network, in both directions

vars == <<lState, fState, restartHandled, fResult, fileOnDisk, msgs>>

\* BlobReply results: 0, ENOMEM (retryable) and any other errno (terminal).
Results == {"ok", "retry", "fatal"}

Messages ==
    {[type |-> "RestartedQuery"], [type |-> "Blob"]}
    \cup [type : {"RestartedReply"}, restarted : BOOLEAN]
    \cup [type : {"BlobReply"}, result : Results]

-----------------------------------------------------------------------------

Init ==
    /\ lState = "RESTARTED_LOOP"
    /\ fState = "WAITING_FOR_MESSAGE"
    /\ restartHandled = FALSE
    /\ fResult = "none"
    /\ fileOnDisk = FALSE
    /\ msgs = {}

-----------------------------------------------------------------------------
(* Leader *)

LeaderSendRestartedQuery ==
    /\ lState = "RESTARTED_LOOP"
    /\ lState' = "RESTARTED_SENT"
    /\ msgs' = msgs \cup {[type |-> "RestartedQuery"]}
    /\ UNCHANGED <<fState, restartHandled, fResult, fileOnDisk>>

LeaderRecvRestartedReply ==
    /\ lState = "RESTARTED_SENT"
    /\ \E m \in msgs :
        /\ m.type = "RestartedReply"
        /\ lState' = IF m.restarted THEN "BLOB_LOOP" ELSE "FINAL"
    /\ UNCHANGED <<fState, restartHandled, fResult, fileOnDisk, msgs>>

LeaderSendBlob ==
    /\ lState = "BLOB_LOOP"
    /\ lState' = "BLOB_SENT"
    /\ msgs' = msgs \cup {[type |-> "Blob"]}
    /\ UNCHANGED <<fState, restartHandled, fResult, fileOnDisk>>

LeaderRecvBlobReply ==
    /\ lState = "BLOB_SENT"
    /\ \E m \in msgs :
        /\ m.type = "BlobReply"
        /\ lState' = CASE m.result = "ok"    -> "FINAL"
                       [] m.result = "retry" -> "BLOB_LOOP"
                       [] m.result = "fatal" -> "FAILED"
    /\ UNCHANGED <<fState, restartHandled, fResult, fileOnDisk, msgs>>

\* Also covers recv(2) failing while waiting for a reply.
LeaderTimeout ==
    /\ lState \in {"RESTARTED_SENT", "BLOB_SENT"}
    /\ lState' = IF lState = "RESTARTED_SENT" THEN "RESTARTED_LOOP" ELSE "BLOB_LOOP"
    /\ UNCHANGED <<fState, restartHandled, fResult, fileOnDisk, msgs>>

LeaderCrash ==
    /\ lState \notin {"FINAL", "FAILED"}
    /\ lState' = "RESTARTED_LOOP"
    /\ UNCHANGED <<fState, restartHandled, fResult, fileOnDisk, msgs>>

-----------------------------------------------------------------------------
(* Follower *)

FollowerRecvRestartedQuery ==
    /\ fState = "WAITING_FOR_MESSAGE"
    /\ [type |-> "RestartedQuery"] \in msgs
    /\ fState' = "RESTARTED_REPLY_LOOP"
    /\ UNCHANGED <<lState, restartHandled, fResult, fileOnDisk, msgs>>

FollowerSendRestartedReply ==
    /\ fState = "RESTARTED_REPLY_LOOP"
    /\ fState' = "WAITING_FOR_MESSAGE"
    /\ msgs' = msgs \cup {[type |-> "RestartedReply", restarted |-> ~restartHandled]}
    /\ UNCHANGED <<lState, restartHandled, fResult, fileOnDisk>>

FollowerRecvBlob ==
    /\ fState = "WAITING_FOR_MESSAGE"
    /\ [type |-> "Blob"] \in msgs
    /\ fState' = "WRITING"
    /\ UNCHANGED <<lState, restartHandled, fResult, fileOnDisk, msgs>>

FollowerWriteCompleted ==
    /\ fState = "WRITING"
    /\ fState' = "BLOB_REPLY_LOOP"
    /\ fileOnDisk' = TRUE
    /\ restartHandled' = TRUE
    /\ fResult' = "ok"
    /\ UNCHANGED <<lState, msgs>>

\* The write is atomic (write, fsync, rename), so a failure leaves the disk as it was.
FollowerWriteFailed ==
    /\ fState = "WRITING"
    /\ fState' = "BLOB_REPLY_LOOP"
    /\ fResult' \in {"retry", "fatal"}
    /\ UNCHANGED <<lState, restartHandled, fileOnDisk, msgs>>

FollowerSendBlobReply ==
    /\ fState = "BLOB_REPLY_LOOP"
    /\ fState' = "WAITING_FOR_MESSAGE"
    /\ msgs' = msgs \cup {[type |-> "BlobReply", result |-> fResult]}
    /\ fResult' = "none"
    /\ UNCHANGED <<lState, restartHandled, fileOnDisk>>

\* Volatile state is lost; the file on disk survives.
FollowerCrash ==
    /\ fState' = "WAITING_FOR_MESSAGE"
    /\ restartHandled' = FALSE
    /\ fResult' = "none"
    /\ UNCHANGED <<lState, fileOnDisk, msgs>>

-----------------------------------------------------------------------------
(* Network: receiving does not remove a message, which models duplication. *)

LoseMessage ==
    /\ \E m \in msgs : msgs' = msgs \ {m}
    /\ UNCHANGED <<lState, fState, restartHandled, fResult, fileOnDisk>>

-----------------------------------------------------------------------------

Next ==
    \/ LeaderSendRestartedQuery
    \/ LeaderRecvRestartedReply
    \/ LeaderSendBlob
    \/ LeaderRecvBlobReply
    \/ LeaderTimeout
    \/ LeaderCrash
    \/ FollowerRecvRestartedQuery
    \/ FollowerSendRestartedReply
    \/ FollowerRecvBlob
    \/ FollowerWriteCompleted
    \/ FollowerWriteFailed
    \/ FollowerSendBlobReply
    \/ FollowerCrash
    \/ LoseMessage

Spec == Init /\ [][Next]_vars

-----------------------------------------------------------------------------
(* Properties *)

TypeOK ==
    /\ lState \in {"RESTARTED_LOOP", "RESTARTED_SENT", "BLOB_LOOP",
                   "BLOB_SENT", "FINAL", "FAILED"}
    /\ fState \in {"WAITING_FOR_MESSAGE", "RESTARTED_REPLY_LOOP",
                   "WRITING", "BLOB_REPLY_LOOP"}
    /\ restartHandled \in BOOLEAN
    /\ fResult \in Results \cup {"none"}
    /\ fileOnDisk \in BOOLEAN
    /\ msgs \subseteq Messages

\* The Leader only reports success if the Follower really holds the file.
FinalImpliesFile == lState = "FINAL" => fileOnDisk

\* The Follower never claims to hold the file when it does not.
RepliesAreTruthful ==
    /\ [type |-> "RestartedReply", restarted |-> FALSE] \in msgs => fileOnDisk
    /\ [type |-> "BlobReply", result |-> "ok"] \in msgs => fileOnDisk

\* Not in the .cfg: TLC finds a counterexample (see the trace it reports).
FailureIsGenuine == lState = "FAILED" => ~fileOnDisk

=============================================================================
