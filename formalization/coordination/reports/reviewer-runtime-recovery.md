# Actual reviewer runtime recovery

The coordinator's live tool transcript reports two failed attempts to resume
the original actual review agent `/root/independent_review`. Both returned:

> Agent errored: The 'gpt-6.1-sol-wm' model is not supported when using Codex with a ChatGPT account.

The second attempt was a follow-up to that same actual agent; it failed with
the same runtime error. Attempting a fresh spawn at the same path was rejected
because the agent path already existed. These are runtime failures, not a
mathematical rejection, an approval or evidence that another agent is the same
reader. This report records the coordinator-provided tool evidence; the
infrastructure implementer did not run or impersonate the original reader.

The old agent had personally read 25 B048 module bodies at an earlier source
checkpoint, without completing the whole package or approving it. Its partial
read is preserved as historical work and cannot certify B048. No approval or
lease is transferred. All B048 implementation contributors remain authors.

Two genuinely fresh agents use distinct actual identities:

| Actor | Actual identity | Scoped work |
|---|---|---|
| `independent_review_recovery` | `/root/independent_review_recovery` | Its own read-only whole-B048 mathematical review, including rereading bodies the old reader had read. |
| `reviewer_recovery_control` | `/root/reviewer_recovery_control` | Its own read-only independent control of this recovery infrastructure PR. |

Neither has authored or directed the implementation of this recovery PR or
B048. Each must establish that fact in reality; the queue checks the complete
recorded author identities and historical-author projects. A label alone is
insufficient. The infrastructure implementation authors are `/root` and
`/root/reviewer_recovery_protocol`; its independent approval is supplied only
by `/root/reviewer_recovery_control` in a separately authored review report.

Policy revision 12 appends these two reader identities with only review and
integration roles and no historical-author projects. Every previous actor,
identity, release permission, capacity rule and legacy-acceptance digest stays
unchanged. The complete BOARD, source pin, mathematical contracts, Lean source,
toolchain, manifest and CI workflow are unchanged by this infrastructure PR.

The explicit recovery manifest reconstructs this exact prospective policy from
the complete old policy and binds the unchanged old/new BOARD and both policy
digests. Its narrowly scoped bootstrap permits the actual fresh control reader
to review this PR, not a batch. Actual exact-head PR CI/audit, the single CAS
integration lock, history-preserving expected-head merge and green actual-main
CI/audit remain required. `promote_reviewer` then changes the live policy
revision and appends deployment history/receipt without changing any package
record, claim, acceptance or authorship. A failed main keeps the lock.

Only after that atomic public promotion may the newly registered mathematical
reader lease B048, complete its own substantive exact-head report and approve
it through ordinary package events. Its report must additionally inspect the
eventual actual submitted head and CI evidence. This report grants neither
infrastructure approval nor B048 approval.
