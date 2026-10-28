# Independent infrastructure source review: actual compiled source closure

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
