# Independent control of reversible Chat/Work profiles

Actual registered reader: `/root/reviewer_recovery_control`.

I authored or directed none of this migration, broker, validators, generators,
tests, repairs or its implementation design. I personally read the complete
32-file diff and the actual old policy/STATE/catalogue. I used no helper reader
and ran no tests, Lean builds or axiom audits. Concrete findings below are
review findings, not implementation contributions.

## Read scope and exact initial binding

Baseline: main `700c12f7e6e8476eb0100a6be37d5f619ade3c0a`.
Initial native freeze: `d5d63756ff77969a2607f4489db17ab096c6ba15`.
Public PR65 initial head: `a2748fb7f6ac2c972c848ff3c111e4701d7da462`.
The public commit has the exact native tree
`bdebb2cb4fb351470ecb31e7921e2b802b225670` and baseline main as sole parent.

I personally read all broker/profile/configurator code, the entire queue delta
against the existing complete validator, all new broker/profile test bodies,
workflow, preparation/handoff generator changes, policy/manifest, protocol,
runbook, queue/request/profile/return documentation, all generated startup
prompts and project instructions. Repeated generated project bodies were read
once in full and their complete identity/path deltas inspected; Work's two
instruction copies are identical. No unreviewed implementation helper supplied
this review.

Actual coordination `7210346655e453aa37536ab916e3a323324dc673` contains STATE396:
48 ACCEPTED packages, no active claim, policy12 and no lock. I fetched the whole
public STATE and verified the saved old snapshot equals that exact Git object;
canonical SHA256 is
`11a23eef3ae5158bc3f17ca0a8f7e5750945a6bd487881661a9e27139a05cddc`.
The old BOARD/policy snapshots equal baseline main bytes, the migration's saved
previous policy is exact, and current BOARD is unchanged.

## Findings

**R1 — P2, OPEN at the initial freeze: malformed checkpoint can poison the inbox.**
In `tools/coordination_broker.py`262–264, `observed_ci.run_id` is interpolated
into a URL before integer validation. A syntactically valid checkpoint request
with `run_id: {"bad": 1}` creates a path containing `{'bad': 1}`. The space causes
Python's HTTP client to raise `InvalidURL`, an `HTTPException`; it is outside
the narrow exceptions caught by `process()`379. The request receives no durable
rejected receipt, and the whole drain aborts before later workers. Every later
drain revisits the same immutable unreceipted request. This contradicts the
documented malformed-request isolation. I reported the concrete source path
and inspected the standard-library exception definition; I did not execute a
reproducer or implement the fix.

Other reviewed invariants at this checkpoint are consistent: fresh Chat
identities4/5/6, all old actors/roles preserved, one unresolved batch per Chat,
real per-package and historical non-authorship, original Work capacity,
accepted-dependency ancestry, single lock and exact PR/main CI, strict policy
revision, manifest-bound deployment, explicit user-authorized reversible modes,
complete stopped-worker WIP handover with old records/history preserved and
effective approvals cleared. These source observations do not establish final
approval while R1 and exact final-head evidence remain outstanding.

## Decision

Approval withheld pending author repair/evidence for R1, independent review of
the actual repaired delta, successful exact final public-head CI and genuine
proposed/published infrastructure lock inspection. Initial CI41168141706 was
still in progress when observed. No conditional statement in this report may
be used as operational approval. Mathematical sources, contracts, provider pins,
toolchain, original Lean workflow and caches have not been changed in the read
migration scope.
