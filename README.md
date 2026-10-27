# CCO formalization — launch snapshot

Destination: https://github.com/shulda/lean_cco; receiving Project 1, package B001.
Read the [Project 1 instructions](formalization/coordination/PROJECT_1_INSTRUCTIONS.md),
[assignment board](formalization/coordination/BOARD.md),
[protocol](formalization/coordination/PROTOCOL.md) and
[B001 assignment](formalization/coordination/packages/B001_SHARED_API.md).
The coordinator supplied the initial Lean/CI scaffold; see [BOOTSTRAP.md](BOOTSTRAP.md)
for exact pins and build/cache/audit policy. Project 1 implements the shared
mathematical API and proofs. The smoke theorem certifies infrastructure only.
No source-paper theorem is formalized yet.
For resuming the coordinating preparation project, read
`formalization/coordination/COORDINATOR_RUNBOOK.md`.

Before implementation run the Python preflight listed in `HANDOFF_MANIFEST.json`.
The board assigns B001 to Project 1; implementation has not started.
Consult [Actions](https://github.com/shulda/lean_cco/actions) for actual build
results. Source files are a focused pinned
snapshot, not a complete compilable human article.

The full hash manifest records the initial snapshot. Verify it before the
first edits; later legitimate board/report/README changes need not match
those initial hashes. Ongoing validation uses module source pins, the
coordination checker and the actual Lean build. Never replace a running
repository with a newly staged initial snapshot.
