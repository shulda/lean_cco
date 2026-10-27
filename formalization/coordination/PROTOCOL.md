# Peer Lean projects — protocol 2

This protocol replaces version 1's mandatory author-mediated allocation and
acceptance. The author approved autonomous lowest-ready claims and peer PR
integration on 27 October 2026. Projects remain equal-status peers. The
preparation project maintains mathematical contracts and resolves exceptions;
it is not a permanent master formalizer.

## Authority

On `main`, `BOARD.json` is the package catalogue: exact claims, source pins,
contract revisions and the dependency DAG. Its state/owner fields are a
bootstrap checkpoint for legacy staging checks, NOT live assignments.
`AUTONOMY.json` says which packages are released, which project IDs exist,
and which reviews require the coordinator. Only the coordinator changes
these permissions, source contracts, shared breaking APIs or the toolchain.

The ONLY live ownership/review/acceptance record is
`coordination:formalization/coordination/STATE.json` in the same repository.
It contains durable claims, submissions, review leases, accepted integration
commits and one integration lock. Do not merge this branch into `main` or
copy its old source tree over a work branch. Read code, contracts and policy
from current `main`; read STATE from the `coordination` ref.

## Autonomous next work

At each active turn fetch the current policy, catalogue, live state, your
checkpoint, and relevant PR heads/CI. Finish any leased review. At the next active checkpoint, review the lowest
eligible foreign submission before resuming an IN_PROGRESS implementation;
this prevents a prerequisite PR waiting through another whole package. If
there is no implementation or review to resume, claim the numerically lowest released AVAILABLE
package whose EVERY prerequisite is ACCEPTED. `tools/coordination_queue.py`
computes this selection and validates state transitions.

A claim is effective only after a successful atomic publication against the
EXACT observed coordination parent/ref with `force=false`. Two concurrent
candidates may both propose B002; only one non-force child can become the
ref head. The loser reloads and recomputes, e.g. now B003. Never reuse a
rejected proposal, force-update, overwrite state, or start speculatively.
One project has at most one IN_PROGRESS implementation and one review lease.
Claims do not expire automatically when a chat is idle or crashes.

Use a new project/package branch from the current GREEN `main`. A completed
SUBMITTED package releases its author's implementation slot: the author may
claim another independent eligible package without consultation. A submitted,
reviewed or merely green feature branch supplies NO accepted prerequisite.
Do not build dependent work on unmerged sibling branches. After acceptance,
new work sees the proofs naturally by starting from updated `main`.

## Mathematical work and submission

Read actual pinned source proofs AND notes, not only claim names. Use the
accepted API and retain exact hypotheses. RAW equality differs from STRONG
diversity; AP/SAP/CCO/NR2 and actual quotient actions are distinct premises.
A conditional provider theorem is not a source instance until its provider
is proved. No sorry/admit/sorryAx or unapproved mathematical axiom may occur
in a completed export's transitive dependency closure.

Keep resumable commits and `reports/ID.md`; each package also needs a durable
`submissions/Bxxx.md` with its exact source-to-Lean map, actual hypotheses,
conditional provider status, consumer, validation evidence and feedback.
Import ALL public modules in `CCO.lean`. Before SUBMITTED require successful
CI and the transitive CCO axiom allowlist on the exact PR head. Submit or
refresh the actual head in live STATE; refreshing invalidates an older review.
Routine local helpers/fixes need no coordinator approval.

## Peer review and integration

A different numbered project, or the coordinator, claims the lowest eligible
submitted PR for review. An author cannot accept their own package. A worker
may review another package while its own implementation is in progress.
The reviewer checks the actual Lean signatures and source quantifiers,
all provider discharge paths, root import closure, a meaningful consumer,
and exact-head build/axiom evidence. A green job alone does not establish
that the theorem expresses the intended mathematics. Record a substantive
review summary anchored to the precise head in STATE. Request changes there
if needed; the author repairs and refreshes the submission.

For integration, acquire the single STATE integration lock, check the current
main commit, and ensure that commit is an ancestor of the reviewed PR head.
If main moved, merge/update main into the PR, resolve conflicts, review the
changed head and rerun its CI. Never silently use an older green run for a
new head. Under the lock merge only the approved exact head (expected-head
SHA), preserving Git history. All projects/coordinator honor this lock.

Wait for a successful build AND axiom audit on the resulting main commit.
Only then atomically mark ACCEPTED with that integration commit and CI run,
and release the lock. This releases dependent packages. If integration CI
fails, keep the lock and package unaccepted, checkpoint the exact failure,
and tell Matěj/coordinator. Never certify, force-reset or roll back others'
work just to clear the queue. Other already-running independent work can
continue; new claims wait for verified main during integration.

## Exceptions and scaling

Mathematical gaps/counterexamples, changes to an accepted shared signature,
toolchain/source changes, failed integration, exhausted eligible work or
permission problems go to Matěj/coordinator. Ordinary completion and the
next released claim do not. Notifications are in the active chat; there is
no automatic background monitor or required private cross-project messaging.

Projects 1 and 2 are initially registered. Further IDs follow a successful
two-project integration checkpoint. Eighteen packages B002–B019 are released
conditionally on their accepted dependencies; the whitelist can pause a
specific seam without stopping unrelated work. The complete procedure and
CAS tool arguments are in [QUEUE_OPERATIONS.md](QUEUE_OPERATIONS.md).
