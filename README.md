# FileTransfer TLA+ spec

TLA+ model of the send-file-over-network protocol (V0): a Leader sends one file to a Follower over the network.

Files:
- FileTransfer.tla: the spec
- FileTransfer.cfg: TLC model config (spec and invariants to check)
- FileTransfer.pdf: typeset version of the spec

What is modeled:
- Leader and Follower state machines
- Message loss, duplication, and process crashes
- Link errors (treated as message loss or timeouts)

Invariants checked:
- TypeOK: variables stay within expected values
- FinalImpliesFile: the Leader only succeeds if the Follower has the file on disk
- RepliesAreTruthful: the Follower never claims to have the file when it does not

Requirements:
- Java 11 or newer
- tla2tools.jar, or the TLA+ VS Code extension

Running:
- VS Code: open FileTransfer.tla and run "TLA+: Check model with TLC"
- Command line: java -cp tla2tools.jar tlc2.TLC FileTransfer

Notes:
- FailureIsGenuine is defined but not checked by default. Add "INVARIANT FailureIsGenuine" to the .cfg to see TLC's counterexample, where the Leader reports failure even though the file reaches the Follower.
- See corresponding Python code [here](https://github.com/nehjoshi/percorr-send-file-over-network).
- See FigJam diagram of leader and follower state machines [here](https://www.figma.com/board/UXkhn2g3OArWUgZJCK5Ilv/PerCorr-Project-2---File-Transmission?node-id=0-1&t=E5eHPbcr2bWSYLFn-1)