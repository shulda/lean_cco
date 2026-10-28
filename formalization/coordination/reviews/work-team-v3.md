# Independent review: one Work team protocol migration

Reviewer: `/root/independent_review`, a fresh control-only agent. I authored
none of the production code, tests, policy or original B002/B003 implementation.
My involvement was independent examination and ordinary review findings; the
implementation author made every code change. Different labels or project IDs
were not used as proof of independence.

Reviewed exact remote PR #6 head:
`137f4ee8d557175593044495a93deface508fb4a`, tree
`3997557e62c5b371b7726e9da38088ea4b037cf7`. I independently fetched the
remote PR and Git commit and verified this tree equals reviewed local
`5d8b7416b71d01d373de7d3a3681aeb7b531d086` (the original migration
`eccb3426b355ace305df2a035e92a30a5c380cc3` plus the WIP checkpoint delta).

**Disposition: source content approved.** Actual exact-head remote CI/audit and
resulting-main CI/audit remain required before deployment is complete. A later
head containing only this review report needs its own exact-head validation;
this report does not approve unexamined production changes.

The full protocol, policy, queue, validator, generated instructions and tests
were examined against the author's migration instructions. All unresolved
batches, including submitted/reviewed/integrating/requested-repair/blocked work,
occupy team slots. The default is two; the optional second claim can fill the
second slot while completion retains priority. A third needs evidence anchored
to both current active heads, disjoint work allocations, an actual dedicated
implementer and a durable independence report. Accepted dependencies and lowest
released eligible selection remain mandatory; a green sibling is insufficient.

Review is a distinct actual non-author role, with unique stable identity,
contributor identities and preserved original author-project provenance. It
cannot be fabricated by renaming the original Project 2 author. Every new
acceptance requires substantive approved exact-head review, submission CI/audit
and resulting-main CI/audit. The sole pre-migration B001 acceptance is narrowly
pinned by its complete-record SHA256 digest, including its historical review.

One exact-parent non-force CAS ledger and one integration lock serialize both
package and infrastructure integration. A head change clears approval; a
merged-main failure retains the lock. Infrastructure deployment is supported
while the original v2 STATE remains readable, followed by one atomic B002/B003
handoff preserving original claim revisions, bases, WIP heads, PRs, previous
owners/authors, last green checkpoints and old history.

I independently reran all 48 Python tests and
`check_formalization_coordination.py --check --require-launch`. I compared the
full package dictionaries, dependency DAG, source_commit, source_files and live
allocation authority with main `7527172215da51d21180a3c5dc624ce54e2869ee`; these
mathematical values are unchanged. The actual v2 STATE at coordination
`e40c1a6a259fc9acf72a3da7758f7d4169cb3188` validates and returns wait pending
handoff. Additional independent probes reject new acceptance without review,
without exact submission CI, with false approval, and deletion of B001's
historical review. The initial acceptance-without-review defect was reported,
fixed by the implementation author and rechecked before this approval.

The separately reviewed WIP `checkpoint` event records an owned IN_PROGRESS
head and completed exact-head observed success/failure CI while preserving the
existing PR, state, claim, base, branch, original/new authorship, history and last
green checkpoint. It neither submits work nor releases capacity. Tests reject
nonowner/old projects, leased/submitted/integrating work, changed PR and
mismatched/pending CI. It permits honest current-head anchors for a later
independence assessment without treating an open proof as complete.

The offline helper checks proposal consistency and evidence shape. The
coordinator must still inspect actual remote refs, ancestry, CI/audit logs,
review authorship and the truth of third-slot activity before publication.
No mathematical package is certified or marked completed by this review.
