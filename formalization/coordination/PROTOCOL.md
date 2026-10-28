# One Work team — protocol 3

The author confirmed both original formalization projects stopped and authorized
this migration on 28 October 2026. One Work team (project 3, coordinator actor
`root`) takes over completion of B002 and B003, preserving both branches,
original authorship, history and all newer WIP. Original project IDs 1 and 2
are historical identities; they are not independent active review workers.
The preparation project continues to prepare mathematical batches.

## Authority and deployment

Current main `BOARD.json` is the mathematical catalogue: exact package claims,
source pin, contracts and accepted-dependency DAG. Its allocation fields remain
a historical bootstrap checkpoint. `AUTONOMY.json` defines the Work team,
roles and limits. Only `coordination:formalization/coordination/STATE.json`
is live ownership/review/acceptance. Read it at an exact observed ref. Never
merge that branch into main or replace public BOARD/STATE from private templates.

Source remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`. This organizational
migration changes no mathematical contract, accepted API, source or toolchain.
The author's express authorization permits the coordinator to deploy it without
another permission request. Existing v2 STATE remains readable, but allows only
the authorized atomic handoff and infrastructure serialization until migrated.
A fresh non-author reviewer checks the policy diff and tests before deployment.

Publish reviewed policy to main under the sole integration lock, validate its
exact PR head and resulting main CI/audit, then atomically hand off BOTH live
claims in one `handoff` event against the observed coordination parent. Keep
claim revisions, bases, original authors, branch/PR/head, actual CI status,
last green checkpoint and old history. A failing WIP head is preserved alongside
its green checkpoint, never reset to it. The event is not a SUBMITTED assertion.

## Work selection and capacity

The default is **two active batches for the whole Work team**. Every unresolved
claimed batch counts, including IN_PROGRESS, SUBMITTED, REVIEWING, INTEGRATING,
CHANGES_REQUESTED and BLOCKED. Submission does not release a batch slot.
Repairs and completion take priority. Do not accumulate backup claims while
waiting for one CI run; continue independent work inside current batches.

A third active batch is exceptional: first verify every prerequisite ACCEPTED
on current main, then record a concrete disjoint work plan, actual implementing
actor, work items and why the work can be active independently of both current
batches. `claim_third` records this durable evidence. A third slot is not an
idle reservation. Four unresolved batches are never allowed. B006/B017 are
backups only after this fresh eligibility/capacity check; do not preclaim them.

New claims select the lowest released AVAILABLE dependency-ready number.
Submitted, approved or green sibling branches never supply prerequisites.
New implementations start from current green main after effective CAS claim.
Existing handoff branches retain their history. Claims do not auto-expire.
`tools/coordination_queue.py` validates proposals; it cannot verify truth of
external evidence. An effective event requires exact-parent non-force CAS.
On collision reload policy, state and actual heads, then recompute; never force,
reparent an old proposal, overwrite history or speculate before ownership.

## Proofs, reports and authorship

Read actual pinned source proofs, notes, package contracts and Lean signatures.
Keep exact quantifiers and RAW/STRONG, AP/SAP/CCO/NR2 and actual quotient-action
distinctions. A conditional provider is not a discharged source instance.
No sorry/admit/sorryAx, new mathematical axiom or disguised stronger premise
may complete a contract. Import all public modules from CCO.lean; retain the
transitive allowlist audit (propext, Classical.choice, Quot.sound).

Use targeted Mathlib and tactic imports in consumers. Respect pinned toolchain
and manifest. Build small increments; investigate actual external Mathlib roots
before targeted cache requests. Record concrete network failures and use remote
CI and independent work, without repeating unchanged long failed attempts.

Keep resumable commits, current reports and per-package `submissions/Bxxx.md`:
source-to-Lean map, actual hypotheses, every open provider, consumer, exact head,
CI/audit and feedback. Publish moving owned IN_PROGRESS WIP heads and actual
success/failure CI with `checkpoint`, preserving claim/provenance and the
existing PR; this is not submission and releases no slot. Record every actual contributor with `record_authorship`
before submission. Preserve legacy-project-1/2 authorship through handoff.
SUBMITTED requires complete contract discharge and successful exact-head CI
and audit; green alone never completes a batch. Refreshing a head clears review.

## Separate non-author control and automatic integration

The `independent_review` actor is a separate review-only agent with its actual
identity recorded in AUTONOMY. It must have written none of the complete batch,
including earlier projects' implementation, and must not participate in its
implementation decisions. Different IDs, agents or role labels alone do not
establish this. A former project 2 author cannot review B003 by renaming itself.
The checker compares contributor identities and original author projects, and
requires a durable actual-identity/non-authorship report. These assertions must
also be checked in reality; the validator cannot certify human provenance.
If the reviewer contributes code, obtain a genuinely fresh non-author reviewer
and update policy/provenance; do not erase authorship to reuse its approval.
Only immutable previously ACCEPTED records retain their pre-v3 review format.

Review the whole package against pinned source, real signatures, all provider
discharge paths, imports, consumer and exact-head CI/audit. Record a substantive
review and its report for that SHA. Reject missing providers; repairs take
priority. A review-only agent may control either batch in the same Work team.

After valid independent approval, the coordinator performs routine integration
automatically. Acquire the **single** STATE integration lock (packages and
infrastructure share it), check current main is an ancestor of the approved
exact head, and re-read both refs before merging with expected-head SHA and
history preserved. If main/head moves, update branch, review the resulting
head and rerun its CI; old green evidence cannot certify it. A pre-merge race
may cancel the lock only with explicit evidence the PR was not merged.

Wait for green build AND axiom audit on the actual resulting main SHA. Only
then ACCEPTED releases dependencies and the lock. Infrastructure completion
records the same main evidence. A merged-main failure keeps the lock and
package unaccepted; checkpoint the precise failure and return it to the
preparation project. Independent existing work continues. Never force-reset,
roll back others' work or certify a failure to clear the queue.

Mathematical gaps, source/toolchain changes, accepted breaking APIs and
unresolved integration failure return to the preparation project. Ordinary
implementation difficulty, repairs and approved integration are autonomous.
