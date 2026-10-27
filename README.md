# CCO formalization

Lean proofs for the CCO manuscript, with source-linked mathematical work
packages and equal-status receiving projects. Lean 4.34.1 and mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612` are pinned.

B001 — shared represented API, SAP geometry and a finite-span consumer —
is [accepted](formalization/coordination/acceptance/B001.md). All public
modules are imported by `CCO.lean` and checked by Lean CI with a transitive
axiom allowlist. This does not claim formalization of the entire manuscript.

Read [protocol 2](formalization/coordination/PROTOCOL.md),
[release permissions](formalization/coordination/AUTONOMY.json),
[package catalogue](formalization/coordination/BOARD.md) and
[queue operations](formalization/coordination/QUEUE_OPERATIONS.md).
The ONLY live allocation/review/acceptance state is on branch `coordination`,
file `formalization/coordination/STATE.json`. Main BOARD is a mathematical
catalogue/initial checkpoint, not live ownership.

[Project 1 instructions](formalization/coordination/PROJECT_1_INSTRUCTIONS.md)
and [Project 2 instructions](formalization/coordination/PROJECT_2_INSTRUCTIONS.md)
allow autonomous lowest-ready claims and peer review/integration. A submitted
branch is not a dependency: accepted results are merged and green on main.
The preparation project resolves source, breaking-API and toolchain changes.

Module [proof notes](formalization/README.md) contain pinned source contracts
and DAGs for eleven prepared modules. B002–B019 are substantial assignments;
module tasks and individual lemmas are internal milestones. The source
snapshot is focused, not the complete typeset human article.

`HANDOFF_MANIFEST.json` records only the original launch snapshot. Ordinary
report/code/coordination changes legitimately differ from it. Ongoing work
uses current source pins, catalogue/queue checks, Lean build and axiom audit.
Never regenerate an old manifest to hide mathematical source changes, or
replace this live repository with a new initial staging snapshot.
