# Coordinator restart — protocol 3

Public repository: <https://github.com/shulda/lean_cco>. Read current main
PROTOCOL.md, AUTONOMY.json, BOARD.json, DECISIONS.md, QUEUE_OPERATIONS.md,
this runbook, actual package contracts, source notes and reports. Fetch the
coordination ref and read STATE at that exact SHA. It is the only live ledger;
BOARD is the mathematical catalogue. Read actual PR heads, diffs and CI logs;
a green branch or stale PR description does not complete a contract.

The author confirmed original projects 1/2 stopped on 28 October 2026 and
explicitly authorized one Work team and the one-time queue migration. Project
3 (`cco-work-team`) owns work; root coordinates/implements/integrates. The
separate `independent_review` role is an actual non-author reader, including
with respect to original code, not the stopped project 2 under a new name.
Preserve all original authors and record all actual new contributor identities.

Default capacity is two unresolved batches team-wide, including submissions,
reviews, integration, repairs and blockers. Complete and repair first. A third
requires a concrete independently active implementer and disjoint work plan,
anchored to the two current batch heads in a durable independence report.
No speculative B006/B017 claims. Every dependency must be ACCEPTED on actual
main with verified resulting-main CI and axiom audit.

Migration order: independently review/test protocol policy/queue/instructions;
serialize deployment under the same single infrastructure lock as any merge;
require exact-head PR CI/audit and green resulting main. Then one atomic
handoff event records both B002/B003, former owners, branch/PR/current heads,
actual observed CI and last green checkpoint, without losing newer WIP or
old claim/base/history. Current v2 STATE stays readable during deployment;
only migration and infrastructure-lock events may modify it. Never reset STATE,
merge coordination into main, or sync private preparation BOARD over public.

Handoff heads (re-read before event): B002 project1/B002-raw-exact PR #3 at
85878128003ace4d4e63d2a42a1cbcb596857308, CI 40665192487 failed; preserve
last green 5254d3a5f2455c97710aa554c884052ac84cd257 (CI 40664176515).
B003 p2-b003-strong-exact PR #4 at f140b2caf36d912f9d60f84727ba7674b8b7205a,
CI 40668681157 passed. These are startup evidence, not certification of a newer
head. Source pin remains 490c3f36d85db5a0b3ced0598e6c431825254ec5.

PR #5 infra/targeted-mathlib-imports at df2dbc4cb3391f74c289dd677a233932e9ab4bd8
passed CI 40673696215 (647 declarations). Read its current diff/logs. Preserve
it; do not write a competing shared foundation patch. Check against BOTH WIP
branches, adding missing imports to consumers. Separate B002's original proof
failures from import regressions. After valid independent review and green
checks, integrate automatically under the same lock. Then target remaining
tactic imports and actual external Mathlib cache roots plus incremental CCO
cache; retain exact transitive audit and pinned toolchain/manifest.

For every routine integration: current main must be an ancestor of approved
exact PR head; take sole CAS lock, re-read refs, merge with expected head and
history preserved, require resulting-main build/audit, then accept/finish.
Head changes require fresh review/CI. If already merged main fails, keep lock
and checkpoint failure for preparation; do not clear dependencies or reset.
Other independent ongoing work continues during CI. No background monitor or
cross-project messaging is installed by this protocol.

B001 remains ACCEPTED at 34b7f1b055788dcf1c134f07fd6a89c123189a82
(main run 40533022306). Its exact historical record is immutable and narrowly
exempted from new provenance fields. New records require actual actor identity,
authorship and substantive independent exact-head report. All external facts
must be verified in reality; the offline queue checks shape and consistency.

Return genuine mathematical gaps, accepted API/source/toolchain changes and
unresolved integration failure to preparation. Routine implementation and
approved integration need no additional author permission. Preserve resumable
commits and current exact-head reports before stopping. Git-backed items do
not need a second storage copy. Do not regenerate old launch manifests or
rerun initial staging over a running repository. Private preparation continues
in shulda/cycle_constrainedness; never enable its paid Actions.

For later prepared-package releases, use the current preparation branch and
its actual contracts/notes/pinned source, preserving the public protocol 3.
No private template is an allocation. With no active claims, independently
review an additive catalogue/whitelist PR, record the old/new complete snapshot
manifest in the sole infrastructure lock, merge the exact approved head and
verify resulting-main CI/audit. Keep old BOARD/policy snapshots from the
locked base. `promote_registry` then validates those explicit old snapshots
and the deployed new pair, appends only AVAILABLE live rows and finishes the
same lock atomically. See QUEUE_OPERATIONS.md; ordinary validators remain
strict during deployment, and every existing acceptance/history record stays
unchanged. Claim the lowest eligible package only after effective public CAS.
