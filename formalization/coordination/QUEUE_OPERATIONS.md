# Queue operations — protocol 3

Read current main policy/catalogue/protocol/runbook and actual reports/PRs/CI.
Fetch coordination head **S**, and STATE at that exact SHA. The Python helper
is offline: a proposal is neither a claim nor certification of evidence.

```bash
python tools/coordination_queue.py --state /tmp/cco-state.json --project 3 --actor root
python tools/coordination_queue.py --state /tmp/cco-state.json --project 3 --actor independent_review
python tools/coordination_queue.py --state /tmp/cco-state.json --project 3 --actor root \
  --event EVENT --data /tmp/cco-event.json --output /tmp/cco-next-state.json
```

Publish exactly one transition: create a blob containing proposed STATE;
create a tree from **S**'s actual full tree replacing ONLY STATE; create a
commit with parent **S**; update coordination using `expected_sha=S` and
`force=false`. Re-read and verify the resulting event/revision. On stale CAS,
reload current policy, STATE and external heads, then recompute. Never force,
reset, reparent a failed proposal or replace the ledger's source tree.

Every event supplies `actor_id` (CLI defaults to `--actor`) and package events
supply `package_id`. SHAs are full forty-character hex. Success CI is
`{"run_id": N, "head_sha": SHA, "conclusion": "success", "axiom_audit": "allowlist"}`
after inspecting actual exact-SHA logs. `observed_ci` for WIP handoff may
record failure; it is not successful submission evidence.

| Event | Required data in addition to actor/package | Meaning |
|---|---|---|
| `handoff` | `previous_projects_stopped: true`, `transfers` containing exactly B002/B003 with `previous_owner_project_id`, `branch`, `pr_number`, current `head_sha`, `observed_ci`, `last_green_checkpoint: {head_sha, ci}` | One-time v2→v3 atomic transfer after policy deployment; preserve original authors, existing claim/base/history and WIP. |
| `claim` | `base_main_sha`, `base_ci` | Lowest released AVAILABLE package, every dependency ACCEPTED, capacity below two; no pending repairs. |
| `claim_third` | claim fields plus `independent_active_work: true`, substantive `summary`, `implementation_actor_id`, `active_work_items`, `independence_report_path`, `existing_batches` | Exceptional third genuinely independent active batch; no fourth. |
| `repair` | `base_main_sha`, `base_ci` | Lowest requested repair, preserving authorship. |
| `checkpoint` | Current `head_sha`, existing `pr_number`, `observed_ci` with exact head/run and `conclusion` success or failure | Owned unleased IN_PROGRESS work only; preserve state, claim, authorship, branch and last green checkpoint; update WIP tracking without submission or another claim. |
| `record_authorship` | `author_actor_ids` | Append actual contributors; never erase original authors or use review-only actor to implement. |
| `submit` | exact `head_sha`, `pr_number`, `ci`, `report_path` = submissions/Bxxx.md (full repository path) | Complete contract only; submission still occupies a slot and clears old review. |
| `review` | exact `head_sha`, `independence` below | Separate actual non-author control leases lowest eligible submission. |
| `refresh_review` | new `head_sha`, new `ci` | Preserve non-author provenance, clear approval and review new head again. |
| `approve` / `request_changes` | exact `head_sha`, substantive `summary` | Compare source/signatures/providers/consumer/evidence on whole package. |
| `start_integration` | approved `head_sha`, `base_main_sha`, `head_contains_main: true`, `ci` | Coordinator/integrator takes sole lock after independent approval. |
| `cancel_integration` | `pr_not_merged: true` | Pre-merge cancellation only; clears approval. |
| `accept` | actual `integration_commit`, successful `main_ci` | Green resulting-main audit releases lock/dependencies. |
| `block` | precise `reason` | Preserve lock on merged-main failure; unresolved batch still counts. |

Use `checkpoint` after inspecting a completed WIP CI run to keep current heads
honest while proofs remain open. It does not certify contract completion,
release capacity, authorize review or create a new claim. It rejects submitted,
leased or integrating work and changes of an existing PR number.

For `claim_third`, `existing_batches` must describe exactly both current active
batches, each with `package_id`, exact current `head_sha`, nonempty `work_items`
and `implementation_actor_ids`. Third-batch work items and its actual dedicated
implementer must be disjoint. The durable `independence_report_path` under reports/
explains file/API and resource independence against those anchored allocations.
The helper checks consistency; the coordinator verifies these facts in reality.

`independence` is `{"identity": "/root/independent_review", "non_author": true,
"summary": "actual substantive independence explanation (at least 80 characters)",
"report_path": "formalization/coordination/reviews/NAME.md"}`. The report must
identify the actual reader and establish no implementation/authorship or design
participation in this complete package, including historical work. A renamed
old author is not independent. All actual authors must remain in provenance.

Infrastructure/policy PRs use this same lock via `start_infrastructure`:
`pr_number`, `head_sha`, `base_main_sha`, `head_contains_main: true`, successful
`ci`, `author_actor_ids`, `original_author_project_ids`, and `review` containing
`actor_id`, exact `head_sha`, `approved: true`, substantive `summary` and the
above `independence`. `finish_infrastructure` needs actual `integration_commit`
and successful `main_ci`; `cancel_infrastructure` needs `pr_not_merged: true`.
A failed resulting main is kept locked, with a durable failure checkpoint.
These operations work during the v2→v3 deployment without resetting STATE.

Before any actual merge, re-read main/PR and lock; merge with expected head and
history preserved. If either ref moved, update main into the branch, review
changed SHA, rerun CI, and reacquire the lock. After actual merge inspect the
push CI and transitive axiom audit at the resulting main commit before finishing.
