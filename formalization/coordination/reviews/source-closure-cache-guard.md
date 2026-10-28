# Independent infrastructure source review: actual compiled source closure

**Current disposition: APPROVED, exact final PR9 head
ce93b92c70a36195979263e9fd578943edc53214.** The final section below supersedes
the earlier withdrawn/pending dispositions; their findings remain preserved.

Actual reviewer `/root/independent_review` authored no implementation or
production tests. Reviewed exact source ddbd9e82467fe83e19636c42e5f491f8b3993c37
plus symlink repair163e5d5043019594d8de96f43f05efa75c5f1637. This is source
approval, not certification of a later remote/current-main head; exact CI,
the sole integration lock and resulting-main checks remain required.

## Concrete failure and new check

I preserved an actual copied-baseline5ff0881 worktree where normal Lake
claimed776 jobs, current root source inputs and a new AgeAP import, yet
actual import CCO could not expose CCO.AgeAP and the official audit saw647
instead of654 declarations. Direct import CCO.AgeAP succeeded. The old
root olean, ilean and C output remained old, and the output descriptors
CORRECTLY described those stale bytes; the earlier byte guard passed33.
Current source hash also matched the trace. Actual resolution selected
the own worktree root, so path shadowing did not explain this witness.
The initiating cause remains UNPROVED; no compiler/CAS/copy cause is asserted.

The new helper uses pinned Lean.parseImports' and readModuleData to compare
the actual compiled header with the CURRENT SOURCE header for every
source-reachable CCO module. Complete import order/flags, implicit imports
and module mode are compared. It independently computes Lake's exact text
source hash and matches the trace's source input, allowing a moved worktree
prefix. It verifies the auditor's actual findOLean resolution selects the
SAME checked physical artifact. Existing actual-byte checks for every
olean partition remain. Missing/unreadable/mismatched reachable modules
fail the complete check; a cold missing prebuild module is allowed.

I read all Python/Lean logic, actual pinned parser/source-trace interfaces,
workflow and tests. The workflow now repairs, builds, requires COMPLETE
current source closure BEFORE the unchanged official audit, then checks
the complete closure again afterwards because the pinned audit script also
builds. No theorem, source contract, toolchain, manifest, targeted roots or
axiom allowlist changes. These checks establish input/import/output
consistency; they do not re-elaborate an arbitrarily fabricated current-
input trace to prove its proof body corresponds to its bytes. The pinned
normal build and official transitive audit remain mandatory.

## Independent findings and verification

I independently ran the new guard read-only on the UNTOUCHED original
witness. It rejects only CCO.trace for compiled-import mismatch, while
the old byte guard had passed. The original source and artifacts remain
preserved. The source-current/descriptor-consistent stale CHILD fixture
was also inspected: old guard passes33, new guard rejects only Examples,
repair removes its eight generated outputs, ordinary776 build exposes the
new child through import CCO, official audit655 passes and full33 closure
passes. This positive child recovery is distinct from the root witness.

I found and reported an actual symlink false positive: the initial
comparison resolved the auditor path but not the expected artifact path.
The corrected163e5d resolves BOTH, retains different-artifact rejection,
and adds a real filesystem symlink regression. I independently reran all
59 local-base tests. The complete guard passes my checked B003 fca158
modules/parts and combined B002 f013317 modules/parts, including its valid
unchanged-child symlinks. Both combined mathematical builds and actual
root API/official audit checks were independently positive.

I additionally copied the original preserved ROOT witness into a separate
own recovery worktree. The new guard classified the semantic-only mismatch
and invalidated exactly ONE root module/eight generated files. A later
normal776-job build STILL failed actual root AgeAP checks. I stopped before
auditing, preserved this second witness and reran the COMPLETE guard:
it again rejects the root for compiled-import mismatch. Thus this failed
root recovery is NOT counted as repaired and is not concealed by the
positive child fixture. The workflow's new required postbuild check fails
closed in precisely this case before an incomplete audit can certify it.
Further recovery investigation uses separate copies and does not alter
the original witnesses. A zero-CCO-artifact source build independently
exposes AgeAP and passes654 audit, so the shared type itself is proved.

## Subsequent concrete finding: directory-alias byte coverage

The earlier conditional source approval of163e5d is SUPERSEDED: **PENDING
repair of complete actual-byte coverage through directory symlinks.** Fresh
reader `/root/full_control_resume` found that Path.rglob skips nested
directory aliases. A valid StrongExact directory symlink therefore left
only33 parts in the byte descriptor scan while the source/header helper
still covered158 modules. Appending a byte to a nested child could pass.
I independently confirmed the enumerator limitation by code inspection;
the actual source/header checks do not substitute for every output's byte
check. The separate different-artifact and individual-file-symlink tests
remain valid but do not cover this directory case. Runtime author owns
the fix; neither control reader authored production code. No mathematical
head approval is changed by this infrastructure finding.

The new exact correction must reject the corrupted nested child, accept a
valid alias, terminate on directory cycles and preserve complete317-module
coverage before renewed source approval/remote CI. This remains consistency
checking with bounded invalidation, not a claim that every inconsistent
cache recovers on its first rebuild. No remote throughput or initiating-
cause claim follows from these experiments.

## Final repaired exact head approved

Actual registered reviewer remains `/root/independent_review`, actor
`independent_review`; I authored no production code or production tests.
I personally read the full frozen recovery/coverage delta
`acff2244bbf193140d40a2069f2cda7542a3063d`, its previous ddbd/163 code,
the final current-main assembly `e1dded510eb9440329a4369b41525d47e661331c`,
and the actual final corroborating report. This is my own substantive
decision, not another reader relabelled as this actor.

The directory finding is CLOSED: canonical compiler-derived SOURCE metadata
now supplies every exact reachable trace path to the byte-descriptor scan.
No recursive symlink following is enabled, so directory aliases cannot omit
reachable children and actual symlink loops cannot cause unbounded traversal.
Valid same-artifact aliases resolve on both sides; genuinely different
audit artifacts are rejected. I inspected the actual finite enumeration and
all malformed/missing/current-source checks.

The safe-invalidation findings are also CLOSED. Ordinary owned directories
retain selective module invalidation. An affected library or IR directory
alias selects only this build's whole CCO namespace discard; nested aliases
are unlinked, not traversed. Parent aliases at lib/lib/lean/ir below the
selected build boundary are rejected BEFORE any deletion. Actual source,
package and non-CCO sentinels and external alias outputs are preserved by
the real regression cases. I personally reran all63 tests on the frozen
author base, including the actual filesystem alias/preflight cases.

The workflow requires complete current-source byte/header coverage after
the incremental rehash build and before the unchanged official audit. Its
ONE bounded fallback, only after a failed complete postbuild check, clears
generated CCO artifacts, retains dependency caches, rehash-builds from zero
CCO outputs and must pass the complete check. Any clear/build/check failure
stops the job. The additional post-audit complete check remains mandatory.
Lake artifact-cache disablement and explicit input rehashing do not replace
the official audit or make a universal recovery/causality claim.

I personally read and adopt the final self-contained corroboration by the
actual separate `/root/full_control_resume`, report-only commit
`27a1647317dee578f765b3b79f1e562dfcf4c918`, file
`formalization/coordination/reports/cache-closure-full-control-20261028.md`.
That reader and its review-only helper authored no production implementation.
Its actual frozen real nested-directory alias+loop fixture accepts158/158
and rejects the appended-byte child, closing the originally reported hole.
Its independent parent-alias preflight cases preserve external outputs;
its exact final B003 build/audit/complete checks pass1037/2069/158, and the
combined accepted-source checks pass317/3657/317. Its true identity and
earlier withheld disposition are retained. I do not label its blackbox
fixture compilation as my own.

Positive bounded recovery is independently documented on a copy of the
AgeAP witness (clear10, zero CCO,776, actual root export,654,33/33) and on
the accepted combined source (clear10, zero CCO,1211, actual RAW/STRONG
APIs,3657,317/317). I inspected those actual logs and source-preservation
assertions. The original witnesses are untouched. My own additional copied
variant remained stale even after its single clean/rehash attempt; actual
AgeAP checks failed and the FINAL complete guard again rejected its root
before audit. This is not counted as positive recovery. Persistent failure
is intentionally fatal in the new workflow; the positive controlled copies
do not establish universal recovery or explain the initiating cause.

## Exact remote CI and integration gate

I independently fetched PR9 metadata and exact Git object
`ce93b92c70a36195979263e9fd578943edc53214`, tree
`7db06ece7ddec278e8a6a84bdeb4ee88938cbf81`, parent accepted main
`4206ff772cc3ee334fe530b55dbb0afe8174dfd4`. This is exactly the local e1dded5
tree. All six executable infrastructure/workflow/test files equal the frozen
author leaf. The only other changes are the runtime report and two accepted-
status submission documents, personally read. There is NO change to CCO
proofs/root, source pin, mathematical contracts, policy, toolchain or manifest.

Actual successful run40701695826/job122862931153 logs were fetched by me:
67 tests; the restored project archive passes317 BYTE parts AND317 CURRENT
SOURCE modules; rehash build1211; complete317/317 BEFORE audit; unchanged
official3657-declaration audit with only propext, Classical.choice,
Quot.sound; final317/317. The healthy-cache CI did NOT execute fallback;
fallback evidence is the separate explicit controlled runs above.
Synthetic merge `ab8f9fb675be1ad9a8ec94f58b3bbbea22bab2c4` has the SAME
approved tree and parents current accepted main4206ff77 plus exact ce93b92.

**APPROVED for sole-lock infrastructure integration at this exact head.**
Both mathematical batches remain accepted. Preserve expected-head merge,
CAS and the one integration lock; verify actual resulting-main push CI,
3657 standard-three audit and317/317 complete current source checks before
finishing the infrastructure lock. No throughput or compiler-cause claim is
inferred from the healthy remote cache hit or the retained local failures.
