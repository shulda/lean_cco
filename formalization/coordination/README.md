# Launching the peer formalization projects

Agreed with the author on 27 October 2026. This preparation project owns the
mathematical specification and work allocation. Separate, equal-status
ChatGPT projects implement Lean in one public repository. There is no
permanent master formalizer. The author carries exceptions and completion
reports back to this preparation project.

The checked-in preparation snapshot has no public destination yet. A staged
receiving copy has a bound destination in `BOARD.json`; consult that board
for its current state. Preparing or staging these files does not create a
repository, publish the manuscript or start a Lean build.

The destination is now <https://github.com/shulda/lean_cco>. Its bound `main`
board is the live allocation record after publication; the private unbound
copy remains a preparation template. To resume this coordinating project,
read [COORDINATOR_RUNBOOK.md](COORDINATOR_RUNBOOK.md).

## Files used in the public repository

| File | Purpose and writer |
|---|---|
| `formalization/coordination/BOARD.json` | Authoritative project registry, package allocation, contract revisions and acceptance state; maintained by the preparation project. |
| `formalization/coordination/BOARD.md` | Generated human-readable view of the same allocation. |
| `formalization/coordination/PROTOCOL.md` | Common working rules. |
| `formalization/coordination/packages/B001_SHARED_API.md` | First project's substantial mathematical assignment and acceptance gates. |
| `formalization/coordination/PROJECT_1_INSTRUCTIONS.md` | Short text to paste into Project 1's project instructions, after binding the public repository. |
| `formalization/coordination/reports/1.md` | Project 1's current checkpoint, written on its work branch. |
| `formalization/coordination/DECISIONS.md` | Decisions affecting shared mathematical contracts or shared Lean representations. |
| `formalization/coordination/COORDINATOR_RUNBOOK.md` | Durable startup, allocation and acceptance instructions for the preparation project. |

The `T01`, `C01`, etc. identifiers in the mathematical modules are internal
proof steps. They are **not** separate assignments to ChatGPT projects.
Project assignments use the larger `B001`, `B002`, etc. packages.

## What is ready, and what remains

The first package is prepared and reserved for Project 1. It covers the
shared typed representations, represented relation/word calculus, actual
quotient-orbital pullback, SAP strong algebra and collision removal, and a
small downstream consumer. This is several pages of source mathematics,
with substantial implementation freedom inside the specified boundaries.

Before Project 1 starts, the author supplies the public `owner/repository`.
The preparation project then stages the launch snapshot with:

```bash
python tools/prepare_formalization_launch.py --repository OWNER/REPOSITORY --output /tmp/cco-formalization-launch
```

This creates a **local staging directory**, binds the repository in the board
and instructions, and marks B001 assigned. It does not upload or contact
GitHub. The staged files must be committed to that exact public repository
before the project is created. At that point the instructions contain
concrete GitHub paths. The Lean toolchain, Lake project and Lean CI are
created **there by Project 1**, as part of B001.

The coordinator may prepare the initial public CI/Lean scaffold before
handoff. Project 1 then validates and extends that scaffold in B001. This
staging command is for first launch only; never replace an existing live
board, report or Lean implementation with a newly staged initial copy.

No additional global manuscript audit is a launch prerequisite. The first
project must validate the proposed representation by actual compilation and
proofs. Remaining manuscript work, including parity/Hasse and exact CRT,
continues independently here.

## Gradual expansion

Start with Project 1 only. Accept the shared API after the proof and consumer
gates and a completed report/PR round trip. Then allocate B002 (RAW exact
geometry) and B003 (STRONG exact calculus/PC) to two projects. Project 1 may
take one of these assignments; it does not become a permanent coordinator.

Add a third and possibly fourth project only after two projects have worked
successfully on separate branches and at least one integration has exercised
the shared API. B004 selectors is a later substantial package. The SIR and
parity/Hasse rows are planning envelopes, not ready assignments.

The board is a near-term allocation plan, not a complete partition or
certification of all 342 manuscript results. Its package graph is a
**scheduling graph**. The module claim DAG remains the mathematical graph;
for example selectors need STRONG exact calculus, not the PC fixed-point
proof that happens to share B003.

## Checks

```bash
python tools/check_formalization_coordination.py --check
python tools/check_formalization_coordination.py --check --require-launch
```

The first checks the preparation state, ownership, package DAG, source pins
and generated instructions. The second deliberately fails until the public
repository has been bound and the assignment activated. Neither checks a
Lean proof or GitHub permissions.
