# Independent review: targeted roots and project cache consistency

Reviewer `/root/independent_review` authored none of the implementation,
workflow, helper or production tests. Reviewed exact local checkpoint
`8af9d4a9e9644d66376a684a4ad27610beada3e0`, extending the earlier reviewed
cache/root-discovery commit630ba3a. This is infrastructure source approval;
the resulting-main CI/audit remains required before integration is complete.

The external-root traversal follows every current CCO import edge before
requesting Mathlib cache roots, handles nested comments/current header import
style, and rejects missing local modules or unknown external namespaces.
I compared its cache namespace list with the actual pinned Mathlib Cache.IO.
It finds the actual 12 roots across 32 PR5 CCO modules. Toolchain-provided
Lean/Std/Init modules need no Mathlib cache request. The workflow retains
pinned Lean/Lake/manifest, the existing exact build and transitive CCO audit,
and caches only compatible project .lake/build outputs.

A later concrete stale-output incident was investigated before approval of
project caching. The report correctly distinguishes consistent old archives
restored after source/root changes (new exports rebuilt) from a deliberately
inconsistent snapshot pairing CURRENT input traces with OLD root and child
olean bytes (ordinary Lake succeeds while new exports are missing). The
initial formation of the worker's inconsistent copy remains unproved.
No mtime, path or CAS cause is asserted without evidence.

The new guard uses the pinned Lake.computeFileHash on actual output bytes,
without trusting hash sidecars. It validates both root and child CCO output
partition descriptors, rejects malformed/missing outputs, and invalidates
only that module's generated library/IR/hash/trace files. Source files and
consistent modules remain intact. The workflow repairs after cache restore,
builds/audits in a fresh action process, then checks materialized outputs
again. LAKE_RESTORE_ARTIFACTS=true ensures external audit commands see the
legacy paths. A post-audit mismatch still fails the entire CI job.

I independently read the Python/Lean helper, metadata/path validation,
workflow sequencing and actual pinned Lake trace schema, reran all 53 tests,
and exercised the REAL helper/CLI. The actual 32-part cache passes; a temporary
wrong-descriptor/current-byte root fails; bounded repair removes that root
while preserving a valid child and a source sentinel. I also inspected the
actual two-module corruption/recovery and changed-source/cross-worktree
experiment evidence: the repaired fresh build exposes both new declarations,
with audit649 instead of baseline647 and all 33 output parts consistent.

This is output consistency checking, not a new security or proof assumption.
The temporary test probe sources are absent from production. No mathematical
source statement, accepted API, toolchain or axiom allowlist was changed.
The revised guard addresses the specific new concern that arose after the
earlier same-head warm-archive review.

## Refreshed exact remote head and CI

Independently checked PR7 remote object and current PR metadata:
`46eff13536816a02123a6abbd8e09a5ac6438e6a`, tree
`14845e20e6b98ad03bd9ef89b6734865d4a5ec3e`. Its synthetic merge
`d2118a42a6db6e35e4a2f7706da89902cfc3c852` has the SAME tree and parents
current main26868153 and the exact reviewed remote head. The coordinator's
current-main local assembly0eb1362 has this same tree; the guard code is
the reviewed8af source with the earlier approved policy/main already merged.

I fetched actual successful run40684208315, job122802323090 logs. They show
57 tests, targeted external cache download, an actual incremental project
cache restore from an earlier compatible key, 32 output parts consistent
before build, normal775-job build, the unchanged official647-declaration
audit with only the standard three axioms, and 32 consistent output parts
again AFTER audit. The new current synthetic-merge cache is saved. This is
real remote restore/guard/build/audit evidence, not a same-head local claim.
No quantitative throughput claim follows from one run.

**Disposition: exact remote head46eff135 is approved for single-lock
infrastructure integration.** Preserve the sole CAS integration lock and
verify resulting main exact CI/audit before releasing it.

## Resulting main verified

Independently fetched resulting main commit
`2ccbbed4ef354a4af8a175ae5e3e9421b8a8c448`, with the same tree
`14845e20e6b98ad03bd9ef89b6734865d4a5ec3e` and parents main26868153 and
approved46eff135. Actual run40686003111/job122808396451 logs check out
that exact main SHA, pass 57 tests and the normal 775-job build, run the
unchanged official 647-declaration standard-three audit, and verify all
32 materialized output parts after audit. This completes the required
resulting-main build/audit evidence for this infrastructure change.
