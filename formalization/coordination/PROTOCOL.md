# CCO coordination — protocol 3, execution profiles

This public protocol supports one Work team and a pool of genuinely separate
Chat projects. The author authorized the Chat/Work tooling transition on
31 October 2026. Source remains `490c3f36d85db5a0b3ced0598e6c431825254ec5`;
mathematical contracts, accepted APIs, toolchain and external provider pins
are unchanged. Projects 1/2 are stopped historical authors. Work is project3;
fresh Chat projects are registered in AUTONOMY, initially4/5/6, never aliases
of those older projects. Existing package records/history are preserved.

## Authority

Main BOARD.json is the mathematical catalogue and accepted-dependency DAG,
not live allocation. AUTONOMY.json registers immutable actor identities,
roles, released IDs and execution_profiles. Top-level two/three capacity and
historical Work notes describe the Work profile. Only the exact observed
coordination:formalization/coordination/STATE.json is live ownership, review,
execution_mode, claims_paused, integration lock and acceptance. STATUS.json
is a derived index and gives no lease. Broker receipts expose a small exact
actor-relevant state_view bound to the full STATE Git blob, so normal Chat
work need not repeatedly import the entire historical ledger. Audits/handovers
still read the whole canonical STATE; a view alone creates no claim. Never reset STATE, copy a private
preparation BOARD over the public catalogue, or merge coordination into main.

Use tools/coordination_queue.py for pure validated proposals. An effective
transition requires a commit whose sole parent is the exact observed
coordination head and a non-force ref update, followed by full readback.
On a CAS collision reload and recompute; never force or reparent the same
proposal. Manual transitions replace only STATE. The request broker may also
write the matching request receipt and derived STATUS in the same commit;
its path allowlist never permits source, policy or BOARD changes.

## Profiles and work selection

In work mode, one project3 team owns implementations: default two unresolved
batches total, at most three. Third-slot work must be actually independent,
with a dedicated implementer, disjoint work items and a durable report bound
to both existing exact heads. No speculative backup claim.

In chat mode, every fresh registered project owns at most one unresolved
batch. The current profile initially has three projects/slots. SUBMITTED,
REVIEWING, INTEGRATING, CHANGES_REQUESTED and BLOCKED all occupy the owner's
slot. A Chat project's implementation and review capabilities are separated
PER PACKAGE by actual complete authorship, stable identity and historical
project provenance, rather than pretending a renamed author is independent.
A new chat in the same project inherits that project's authorship.

Choose the lowest released AVAILABLE package whose entire dependency DAG is
ACCEPTED on actual main with successful actual-main build/audit. A green or
approved unmerged sibling is not a dependency. Complete and repair first.
Finish owned locks and leased reviews; repair your own work; perform eligible
non-author review while waiting for CI; continue your own implementation;
otherwise claim only the actual free slot. Do not repair another project's
branch without a truthful formal handover. Claims do not expire on silence.

A stopped idle Chat project needs no policy deletion. It must first have no
own claim, live review lease or integration lock. Registrations/authorship
remain. Adding another genuine project uses the tested append-only profile
proposal/generator; existing actor identities and Work limits never change.
See EXECUTION_PROFILES.md and CHAT_PROJECTS.md for concrete instructions.

## Publication, proofs and control

Read actual pinned source proofs/notes/contracts, current code and exact Lean
signatures, not only PR descriptions. Preserve exact quantifiers, RAW/STRONG,
AP/SAP/CCO and real quotient actions. A conditional provider is unfinished
until the required source instance is proved; source-conditional theorems
keep their actual explicit hypotheses. No sorry/admit/sorryAx, new axiom,
missing provider or disguised stronger premise may complete a contract.
Every public module is imported from CCO.lean. Preserve the transitive
propext/Classical.choice/Quot.sound allowlist audit.

Use specific Mathlib/tactic imports in their consumers, pinned toolchain and
manifest, small increments and coherent source commits. Keep one publisher
per PR branch and separate worktrees/build outputs for concurrent authors.
Verify imports against affected consumers. Discover actual external Mathlib
roots before targeted cache requests; cache get CCO.lean is insufficient.
Document concrete network failures and use remote CI/independent work rather
than repeating unchanged long installation attempts.

Keep every old and new contributor identity before submission, including
historical projects. record_authorship appends, never erases. Preserve native
history, newer WIP and green checkpoints. checkpoint records actual observed
head/PR CI without claiming completion or freeing a slot. SUBMITTED requires
all actual contract obligations, exact green PR build/audit and a durable
submissions/Bxxx.md source-to-Lean map with actual hypotheses/providers.

The reviewer must personally read the whole package/source/providers/consumer
and exact CI, be an actual non-author of all its history and design, and
publish their own actual-identity/non-authorship report for that exact SHA.
This is not proved by labels, project numbers, green CI or a borrowed report.
A former author cannot review their own work under a new actor. Work uses a
separate actual review-only agent. Chat projects may cross-review only
packages they never authored or directed. If a reviewer writes repairs,
record that authorship and obtain a genuinely different non-author reader.
Head changes invalidate approval; reread true deltas and require fresh CI.
Only pinned immutable legacy ACCEPTED records keep the old review format.

After valid independent approval, integrate autonomously under the ONE STATE
integration lock shared by packages and infrastructure. Current main must be
an ancestor of the approved head; reread main/PR/lock immediately before the
expected-head history-preserving merge. No squash/rebase. If refs move, update
branch, review the resulting head, rerun CI and reacquire the lock. Cancel only
with actual evidence the PR is unmerged. A merged-main failure keeps the lock
and remains unaccepted. Only green build AND transitive audit on the ACTUAL
resulting main SHA permits accept/finish and dependency release.

## Chat request bridge

Chat may append unique JSON files to coordination-requests. Trusted main code
validates the latest full ledger and real CI/PR evidence, then publishes an
exact-parent non-force CAS with a durable receipt. claim_next selects fresh
work only at processing time. Specific events pin expected STATE revision;
rejected/no_change/missing receipts are not claims. Request paths are immutable
and replay is idempotent. Every workflow run drains the whole latest inbox,
including requests whose pending GitHub run was replaced. The broker executes
no inbox code and does no mathematical approval or source merge. Full protocol
also remains usable with the offline Python helper. See CHAT_REQUESTS.md.

## Runtime switches and WIP ownership

Only an actual user instruction authorizes mode changes. pause_claims stops
new claims while existing proof/review/CI work can finish. With no active
claim or integration lock, switch_mode changes only the execution profile,
pause flag and appended event/history, preserving every package record.

For WIP, pause first, publish/checkpoint ALL latest work including failing
heads and actual last green information, obtain actual stop acknowledgement
from all old workers, finish any integration lock, then handover_mode transfers
EVERY active claim to permitted target owners in one CAS. Preserve branch,
PR/head, original claim/base/CI, all old authors and entire old record/history.
New owners are added conservatively to authorship. Clear effective review and
approval and return to IN_PROGRESS; the old review remains only in history.
Do not reset to an older green head. Chat targets get at most one claim each;
three Work claims still need the genuine anchored third-slot plan. More claims
must first drain to target capacity. See RETURN_TO_WORK.md for both directions.

## Reviewed policy deployments and catalogue releases

Initial profile deployment is a reviewed infrastructure PR with no active
claims. execution_profile_manifest binds unchanged complete BOARD and complete
old/new policies; only fresh Chat actor/project pairs, their explicit profiles
and a scope note may be appended. Preserve every old role/identity, source,
release and Work rule. Later worker additions preserve live claims and mode.
Use the NEW helper with OLD snapshots for start_infrastructure. After exact PR
review/CI, expected-head merge and green actual main CI, promote_profiles with
explicit old/new snapshots advances policy revision and ends the SAME lock
atomically. It changes no package record; normal revision checks stay strict.

Prepared-package release uses registry_promotion_manifest and promote_registry:
no active claims, append only concrete new contracts/released IDs and AVAILABLE
live records, preserve all old catalogue/policy/claim/acceptance/history data.
A private preparation snapshot is never a public release. Keep the reviewed
complete old/new snapshots and main CI in the sole infrastructure lock.

Unavailable actual review runtimes use reviewer_recovery_manifest and
promote_reviewer. Preserve old identities/partial reports, document actual
failure/stop and retries, append only one/two genuine fresh non-author readers,
and bind complete old/new policies plus unchanged BOARD. The narrow bootstrap
allows that actual fresh reader to review ONLY its recovery PR before formal
activation, never to provide a package approval. No active review lease or
approval may transfer. Finish after actual resulting-main CI in one CAS.

These deployment kinds are mutually exclusive and generic finish cannot
complete their locks. A failed main remains locked; no shortcut or revision
mismatch is accepted. Genuine mathematical gaps, source/toolchain/accepted API
changes and unresolved merged-main failure return to preparation. Routine
implementation, repairs and valid integration need no extra user permission.
