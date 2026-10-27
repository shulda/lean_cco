# Autonomous peer formalization

B001 has been accepted on main; see [the acceptance record](acceptance/B001.md).
Separate equal-status projects implement substantial source-linked packages
in <https://github.com/shulda/lean_cco>. The preparation project continues
mathematical consolidation and handles exceptions; no permanent master
formalizer is needed.

| Location | Meaning |
|---|---|
| main `AUTONOMY.json` | Released packages, registered projects and coordinator review gates. |
| main `BOARD.json` | Mathematical package catalogue, claim ownership by package, source pins and scheduling dependencies. Its allocation fields are only the bootstrap checkpoint. |
| **coordination branch `STATE.json` in this directory** | **Only live allocation, submitted/reviewed state, integration lock and accepted commits.** |
| main `PROTOCOL.md`, `QUEUE_OPERATIONS.md` | Rules and exact non-force CAS publication steps. |
| main `PROJECT_1_INSTRUCTIONS.md`, `PROJECT_2_INSTRUCTIONS.md` | Short stable text to paste into the corresponding ChatGPT project. |
| work branch `reports/ID.md`, `submissions/Bxxx.md` | Current project checkpoint and durable per-package source-to-Lean report. |
| main `packages/Bxxx.md`, module proof notes | Concrete several-page mathematical assignments and exact proof details. |

B002–B019 are released subject to all their dependencies being ACCEPTED.
The lowest ready AVAILABLE number is always selected. Initially projects 1
and 2 are registered. Start a new branch from current green main only AFTER
a successful atomic claim. On a simultaneous claim collision, reload and
recompute. Claims do not expire; no speculative work starts before ownership.

A SUBMITTED author can continue with independent released work. A different
project reviews/merges the old package, checks exact-head CI and resulting
main CI/audit, and then records ACCEPTED. Submitted or merely green branches
never supply dependencies. `coordination` is a ledger branch; never merge
its tree into main. Read policy/code from main and only STATE from that ref.

Further project IDs follow a successful two-project integration checkpoint.
The 19 packages cover the current eleven prepared modules, not all 342
manuscript results or a numerical measure of formal proof difficulty.
Python metadata checks and finite controls are not mathematical certification.

Use `python tools/check_formalization_coordination.py --check --require-launch`
for the main catalogue and `tools/coordination_queue.py --state LOCAL_STATE`
for a downloaded exact-ref live state. Neither checker invents CI evidence.
`prepare_formalization_launch.py` remains a legacy INITIAL staging tool;
never run it over this live repository, reports or Lean implementation.
