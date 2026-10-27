# Queue operations — protocol 2

These steps use the connected GitHub tools or an equivalent Git client. The
Python helper is deliberately offline: a proposed JSON file is NOT a claim.
All external facts (PR heads, ancestry, CI and review content) must be read
from GitHub and checked; the helper validates their shape and consistency,
not their truth. No GitHub token or secret is required in a file.

## Read one consistent state

1. Fetch `main` ref, current `AUTONOMY.json`, `BOARD.json`, `PROTOCOL.md`
   and your report. Fetch the `coordination` ref and remember SHA **S**.
2. Read `formalization/coordination/STATE.json` at that EXACT **S**, not by
   a later moving branch URL. Save it locally as `/tmp/cco-state.json`.
3. Run `python tools/coordination_queue.py --state /tmp/cco-state.json
   --project ID`. It returns resume, resume_review, repair, review, claim,
   or wait. Finish a leased review; at the next checkpoint take the lowest foreign
   submission before resuming implementation. Claim new implementation
   only when neither is pending. Never skip a lower
   available dependency-ready number or invent project IDs.

The queue helper runs from the current main source checkout. The catalogue
and permissions it reads are main files; only the live state comes from S.
On CAS failure fetch current main policy too before recomputing.

## Publish exactly one transition atomically

Prepare an event payload in a temporary JSON file. Run:

```bash
python tools/coordination_queue.py --state /tmp/cco-state.json --project ID \
  --event EVENT --data /tmp/cco-event.json --output /tmp/cco-next-state.json
```

Then use the GitHub connector in this order:

1. `create_blob` for exactly the proposed STATE text. Read commit **S** to
   obtain its actual tree **T**.
2. `create_tree(base_tree_sha=T)` replacing ONLY
   `formalization/coordination/STATE.json`. Do not use a new incomplete
   source tree or mutate main/source files in this transition.
3. `create_commit(parent_sha=S, tree_sha=NEW_TREE)`.
4. `update_ref(branch_name="coordination", sha=NEW_COMMIT,
   expected_sha=S, force=false)`.
5. Re-read the ref/state. Verify the intended claim/review and its
   `claim_revision`. Only a successful non-force publication gives you
   ownership. A failed/stale update requires reload and recomputation;
   never force, reparent an old proposal or reuse its old package choice.

Concurrent commits with the same parent cannot both advance a non-force
ref: after the first, the other is not a descendant. The expected SHA also
rejects stale publication. All other state changes use the same procedure,
so claims, submissions, reviews and integration locks serialize together.
Commit messages should identify project, event and package. There is no
lease expiry or issue-comment locking protocol. Main CI is not run for
these coordination-only commits.

## Event payloads

Every event includes `package_id`. SHAs are full forty-character hex strings.
A CI record is `{"run_id": NUMBER, "head_sha": SHA,
"conclusion": "success", "axiom_audit": "allowlist"}` after inspecting
the actual run/log on that exact commit. Do not invent a successful audit.

| Event | Additional fields | Effect |
|---|---|---|
| `claim` | `base_main_sha`, `base_ci` | Claim the lowest released eligible package from current green main. |
| `repair` | `base_main_sha`, `base_ci` | Resume your lowest requested repair before new implementation. |
| `submit` | `pr_number`, `head_sha`, `ci`, `report_path` = `formalization/coordination/submissions/Bxxx.md` | Submit/refresh an owned unlocked package; invalidate any previous review; author may claim independent next work. |
| `review` | exact submitted `head_sha` | Lease the lowest foreign submission; project 0 denotes the coordinator. |
| `refresh_review` | new `head_sha`, new `ci` | Leased reviewer records a base-update/new head; approval is cleared. Review it again. |
| `approve` | `head_sha`, substantive `summary` | Record source/API/provider/consumer review on that exact head. |
| `request_changes` | `head_sha`, substantive `summary` | Return the package for repair; preserve its owner. |
| `start_integration` | `head_sha`, `base_main_sha`, `head_contains_main: true`, `ci` | Acquire the global integration lock after approved exact-head review and green CI. |
| `cancel_integration` | `pr_not_merged: true` | Cancel only a pre-merge integration, e.g. a base race; clear approval and recheck. |
| `accept` | `integration_commit`, `main_ci` | After actual merge and green main audit, record ACCEPTED and release the lock. |
| `block` | `reason` | Checkpoint a genuine blocker; merged-main failures retain the integration lock. |

## Review and integration sequence

Review the actual source statements and Lean proof dependencies, not only
names and axiom counts. The author may not accept their own package. A
coordinator-only package cannot be taken for peer acceptance. A reviewer
may also have an independent implementation in progress.

Bring current main into the PR first, review the resulting head and wait
for its exact green CI. Then publish `start_integration` and recheck that
main is still the recorded base and PR is still the recorded approved head.
If the base changed before obtaining the lock, cancel BEFORE merging, update
the branch and repeat review/CI. The real merge tool uses expected PR head;
all math and coordinator merges obey the global lock, so main remains
stable between this check and merge. Do not merge source branches based on
an older successful run.

Merge the PR with history preserved. Read the merge SHA from GitHub; wait
for the push CI on that SHA to succeed including the CCO transitive audit.
Then publish `accept`. Keep the lock on a merged-main failure and tell
Matěj; a coordinator repair is needed. Never release dependencies based
only on PR CI, a branch name, an unmerged commit or a report's assertion.

Submissions and peer review records persist in STATE and Git history. The
numbered report may move to a later package; `submissions/Bxxx.md` and its
exact reviewed commit remain the durable package record. No background
monitor or automatic message to another project is installed.
