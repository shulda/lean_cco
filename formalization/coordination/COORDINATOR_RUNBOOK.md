# Coordinator restart — protocol 2

Read actual current GitHub state, not historical chat summaries or old
attachments. Public repo is <https://github.com/shulda/lean_cco>.

1. Read current main `formalization/coordination/PROTOCOL.md`,
   `AUTONOMY.json`, `BOARD.json`, `DECISIONS.md`, this runbook and the
   exact-ref STATE on branch `coordination`. Main BOARD is the mathematical
   catalogue; STATE is the ONLY live allocation/review/acceptance record.
2. Read active reports/PRs at their actual heads and inspect exact CI logs.
   Submitted, integrated and accepted are distinct. A worker may already
   own another independent package while an older submission awaits review.
3. B001 is accepted at `34b7f1b055788dcf1c134f07fd6a89c123189a82`, reviewed
   head a1a709a, successful main run 40533022306. Its source map and feedback
   are in `acceptance/B001.md` and `submissions/B001.md`. Recheck subsequent
   accepted records in STATE; these startup SHAs do not certify newer heads.
4. In private `shulda/cycle_constrainedness`, branch
   `cco-sym/consolidated-r45-20261017`, path
   `cco-symmetric-eppa/papers/consolidated_working`, read
   `COORDINATOR_START_HERE.md`, CURRENT_STATUS and actual module/source proofs.
   Human source pin remains 490c3f36; no source theorem repair was required
   for B001. Next preparation is owner_master/04, then rooted consumers.

The author explicitly replaced version 1's mandatory stop-and-ask after
completion. Eighteen B002–B019 contracts are released through AUTONOMY,
with accepted-dependency and lowest-number rules. Projects 1 and 2 are
registered; the author must update Project 1's pasted instructions to v2.
Other projects do Lean; this preparation project specifies mathematics,
keeps contracts/DAG/feedback current and resolves exceptions.

Peers may review and integrate each other's PRs. Authors cannot accept
own packages. All claim/review/acceptance writes use the documented exact
coordination parent/ref, `force=false`, and retry from fresh state on a
collision. All main integrations honor the single queue lock, exact reviewed
head, current-main ancestry and green resulting main axiom audit. Keep a
merged-main failure locked and unaccepted; repair explicitly. No automatic
lease expiry, background monitor or cross-project message service exists.

Before a policy/source/registry change, coordinate a queue pause with active
workers or use the integration lock; do not let workers use conflicting
permission revisions. Publish concrete reviewed contracts before releasing
the corresponding IDs. Breaking APIs, theorem repair and toolchain updates
remain coordinator gates. Register project 3/4 only after successful actual
two-project integration. Routine next work does not need Matěj's approval.

Private PREPARATION boards remain templates; do not sync them over the public
catalogue, STATE, numbered reports or Lean. The legacy initial manifest is
not an ongoing change prohibition; use source pins, current catalogue/queue
validation and actual Lean build instead. Do not regenerate an old manifest
to hide source changes. Never rerun launch staging over a running repo.

The private checkout may have synthetic history and only selected upstream
files. Publish only verified changed blobs on the full actual remote base
tree, verify the entire tree and update ref against the expected head.
Private commits use `[skip ci]`; never enable private paid Actions. Do not
modify other completed Lean repositories. Git-backed work needs no second
copy in another storage system.
