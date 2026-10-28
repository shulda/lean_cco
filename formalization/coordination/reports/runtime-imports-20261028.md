# Local runtime, WIP import compatibility and cache checkpoint — 2026-10-28

Source pin `490c3f36d85db5a0b3ced0598e6c431825254ec5`, Lean toolchain,
manifest, mathematical statements, proof bodies and axiom allowlist are unchanged.
This is infrastructure evidence, not a completed B002 or B003 submission.

## Exact compatibility candidates

- Existing PR #5: `df2dbc4cb3391f74c289dd677a233932e9ab4bd8`; original remote
  branch was not modified by this follow-up. Its full local build succeeds
  (775 Lake jobs) and the transitive audit checks all 647 CCO declarations.
- B003 original `f140b2caf36d912f9d60f84727ba7674b8b7205a` was merged with
  PR #5, then six import lines added to four consumers. Candidate
  `1e0ac1d2547a5a327378a2c5ec8ffb34badeea04` builds successfully (1009 jobs),
  repeats successfully incrementally, and audits all 1464 CCO declarations.
  Consumer imports: `FinitePC` uses `Mathlib.Basic.Finite.Prod` and
  `Mathlib.Data.Fintype.Powerset`; `ThetaVertices` uses
  `Mathlib.Basic.Finite.Sigma` and `Mathlib.Basic.Finite.Sum`;
  `ThetaCycleContainsRoot` uses `Mathlib.Data.Finset.Max`;
  `ThetaCycleAdvanceReturn` uses `Mathlib.Data.Nat.ModEq`.
- B002 original `85878128003ace4d4e63d2a42a1cbcb596857308` was merged with
  PR #5. Candidate `61ba25625e726150172405e8adf34a3e1fa82cd2` narrows all
  41 `Mathlib.Tactic` umbrellas and supplies missing finite/range imports
  in their consumers (45 files, 30 added and 41 removed import lines).
  Its full build reaches exactly the inherited three failing modules and
  five proof errors, with no remaining import regression: singleton/list
  and induction-argument errors in `WalkCertificateTransport`, Fin.cast
  transport in `FanHomWordTrace`, and dependent-point/argument errors in
  `FanCentreColours`. Their candidate line numbers are 42,72; 99; 41,56.
  Baseline CI 40665192487 has the same errors at 43,73; 100; 42,57.
  A B002 root axiom audit cannot certify this failed build.

Every original B002 Lean module body (135 files), and every original B003
Lean module body (130 files), was compared byte-for-byte after excluding
import lines. They are unchanged. The root module is additional to those
counts. A fresh non-author control agent independently repeated the
comparison and inspected the actual build logs. Remote exact-head CI is
still required after the coordinator publishes the integrated candidates;
local compatibility does not certify a later changed head.

## Runtime and incremental build

The official Linux archive for Lean 4.34.1 downloaded successfully over
HTTPS (580432872 bytes). The local binary reports Lean 4.34.1, release
commit `5045d0056413266e57c625dcd7c365b10e377c52`; Lake reports
`5.0.0-src+5045d00`. Mathlib is the manifest revision
`d13f23b723b8a846827a245b89c10fc7d3f11612`; Lake fetched all remaining
packages at their manifest revisions without updating the manifest.

The execution sandbox returns a namespace PID for which `/proc/<pid>/exe`
is unavailable, although `/proc/self/exe` works. Unmodified Lean queries
the former in its pinned `src/runtime/io.cpp:1411` and fails with
`failed to locate application`. A local-only LD_PRELOAD adapter forwards
only that exact readlink query to `/proc/self/exe`; it does not change the
compiler binary, kernel, definitions or proof checker. CI uses the official
unadapted toolchain. The adapter can be reproduced with:

```c
#define _GNU_SOURCE
#include <dlfcn.h>
#include <stdio.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>
ssize_t readlink(const char *path, char *buf, size_t size) {
    static ssize_t (*original)(const char *, char *, size_t);
    if (!original) original = dlsym(RTLD_NEXT, "readlink");
    char own[128];
    snprintf(own, sizeof(own), "/proc/%d/exe", getpid());
    return original(strcmp(path, own) == 0 ? "/proc/self/exe" : path, buf, size);
}
```

Compile with `gcc -shared -fPIC -O2 -o proc_self_compat.so proc_self_compat.c -ldl`
and set `LD_PRELOAD` to its absolute path for local commands. Extract the
archive with `tar --no-same-owner --zstd -xf ...` in this environment.
Local runtime root is
`/workspace/scratch/6b2f11185e14/runtime/lean-4.34.1-linux` and the adapter is
`/workspace/scratch/6b2f11185e14/runtime/proc_self_compat.so`. These paths
are conveniences, not durable binary dependencies of the project.

Both a small first build of `CCO.TypedRelation` and its warm repeat succeed
(349-job target graph; repeat under one second). Worktrees have independent
`.lake/build` directories and share the pinned package cache read-only after
hydration. Cache download processes are serialized: this sandbox can report
the same namespace PID in different processes, whereas Mathlib uses PID
suffixes to distinguish concurrent cache downloads.

All local audits use the same official tool pin as the workflow:
axiom-audit v0.1.2, `46024e005996495c65ef609368e11ab39c4222e3`. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed.

## Targeted external roots and project cache

The pinned `Cache.Hashing.getFileImports` filters out CCO module edges.
Therefore passing `CCO.lean` alone cannot discover arbitrary internal CCO
imports. `tools/mathlib_cache_roots.py` follows the actual root's complete
local import closure, then prints sorted deduplicated external cache roots.
It excludes toolchain-provided Lean/Std imports and rejects missing local
modules, unknown external namespaces and (with `--reject-broad`) umbrellas.
Its four tests cover nested comments/header boundaries, local dependency
traversal with a cycle, deduplication and failure cases.

| Candidate | CCO modules including root | External Mathlib roots |
|---|---:|---:|
| PR #5 | 32 | 12 |
| B002 narrowed compatibility | 136 | 20 |
| B003 repaired compatibility | 131 | 20 |

The initial union of PR #5/B003 and explicit tactic roots downloaded 817
linked cache files, then the newly discovered finite-instance and modular
arithmetic roots downloaded seven and 39 additional files. Successful local
full builds above use these targeted downloads, not a full Mathlib cache.
The script's exact PR #5 roots were also passed directly to `cache get`.
These are local observations, not remote throughput measurements.

An archive containing only the PR #5 project's `.lake/build` was 2.1 MiB.
After moving the original build directory aside and restoring the archive,
`lake build` succeeds (775 jobs) without rebuilding any CCO module.
The proposed workflow caches only `.lake/build`, with an OS/architecture,
toolchain/manifest/lakefile compatibility key and a commit-specific suffix.
Lake still validates current source/dependency traces. Restoring cached
artifacts never replaces the actual build or transitive axiom audit; the
official audit action itself performs another build before auditing.

The original toolchain cache is retained. Package workspaces are not placed
in the project cache. The workflow uses the existing pinned lean-action to
install the toolchain, retrieves the discovered external roots, restores
compatible project outputs, and invokes the pinned build plus audit action.
No clean full-rebuild, remote cache hit or throughput claim is made until
that changed workflow passes CI. Python tests: all 53 pass on this branch;
workflow YAML syntax and retained audit settings were checked locally.

## Changed-source restore tests and output consistency guard

All of these bounded local checks used actual `import CCO; #check` probes,
not just a Lake success message:

| Experiment | Result |
|---|---|
| Add a public module/root import, then restore OLD PR #5 build archive | New module and root rebuilt; new export available. |
| Change an existing child module, leaving root source unchanged, then restore OLD outputs | Changed child/root rebuilt; new child export available. |
| Restore OLD archive in a separate worktree; change both root imports and an existing child | Both exports available; official audit sees 649 declarations, versus baseline 647. |
| Deliberately pair CURRENT traces with OLD root and child olean bytes | Ordinary Lake build succeeds, but both new exports are absent. |
| Run consistency repair, then build in a fresh shell invocation | Exactly the two inconsistent modules are invalidated/rebuilt; both exports return; official audit sees 649, and all 33 olean parts match their trace descriptors. |

The last case deterministically reproduces the failure mechanism reported
by the parallel workers. The initial formation of their inconsistent copy
was not established; neither mtime nor path precedence is asserted as its
cause. The effective project `LEAN_PATH` and captured compiler paths were
checked. No Lake system CAS directory was present during this reproduction,
so CAS artifact preference is not claimed as the established local cause.
One nested Python orchestration did not expose repair to its following
build; the independently repeated repair and subsequent fresh shell build
verified the stated successful result. The workflow uses separate steps.

Pinned Lake's `Build/Common.lean` checks matching input traces and output
existence, without rehashing output bytes (`checkHashUpToDate'`). Therefore
an inconsistent manual snapshot is not certified merely by rerunning Lake.
`tools/verify_project_cache.py` calls the tiny toolchain-only Lean helper
`project_cache_hashes.lean`, which uses the exact pinned
`Lake.computeFileHash` on actual bytes, ignoring `.hash` sidecars. It compares
all root and child CCO olean parts with each trace's output descriptors.
Malformed metadata, missing outputs and mismatches invalidate only that
module's generated library/IR/hash/trace files. Consistent children remain
untouched. This is the existing Lake consistency hash, not a new security
claim or proof assumption. Five additional tests cover root/child detection,
missing/malformed outputs, path-safe descriptor rejection, and preservation
of valid modules and source files. All 53 Python tests pass locally.

The workflow repairs inconsistent outputs after cache restore and checks
consistency again after the official build/audit. It sets the supported
`LAKE_RESTORE_ARTIFACTS=true`: external plain `lake env` tools load legacy
build-directory outputs, while a configured Lake CAS can otherwise use
preferred internal paths. The output consistency guard remains necessary
because Lake's `restoreArtifact` keeps an existing local file without
comparing its bytes. No CAS data is added to the project-cache archive.

These checks supersede the earlier proposed unconditional root-only delete
guard. They preserve valid project incrementality and detect stale child
exports as well as stale roots. A green new exact-head remote workflow is
still required; no remote cache hit or throughput result is inferred from
these local experiments. The temporary probe sources are not part of this
change or its mathematical exports.


## Semantic source-closure verification after the AgeAP witness

The independent reviewer preserved checkout
`5ff0881ee48d74823350a2820ac37c5bdd488d29` in `cco-review-ageap` after copying
an earlier `.lake/build`. Its ordinary pinned build reported 776 successful
jobs and current root inputs, but the audit saw only the old 647 declarations.
Direct `import CCO.AgeAP` succeeded; `import CCO; #check CCO.AgeAP` failed.
The source listed `CCO.AgeAP`; the actual root olean, ilean import list and
C output still had the earlier closure. The old output-descriptor guard
correctly checked 33 byte-consistent parts and therefore could not detect it.

The root source input hash was independently recomputed with pinned
`Lake.Hash.ofText` and **matched** its current trace input,
`480033033fea0674`. The stale root olean SHA-256 was
`73e6933ae60ab4b9ad258006611831a4c804d1f854e15ffd4df18e26e0a7bccd`;
its descriptor `7edbbffa0b49d8a0.olean` correctly described those stale bytes.
The setup JSON included the correct new AgeAP artifact, and effective
resolution selected this worktree's root. Source-hash or output-hash checks
alone consequently do not establish current import coverage.

`project_cache_metadata.lean` now uses the pinned compiler's own
`Lean.parseImports'` and `Lean.readModuleData`, without importing CCO artifacts,
to follow every current source-reachable CCO module and compare its complete
actual compiled import records, including implicit imports, order, flags and
module mode. It also computes current source hashes independently of sidecars.
The guard checks these against the source input in each trace, allowing old
absolute worktree prefixes but requiring the same source-relative filename.
It initializes the same search path as the official auditor and requires
`Lean.findOLean` to resolve to the exact checked artifact, preventing a different
worktree or package artifact from shadowing it. The existing actual-byte
checks against every olean partition descriptor remain in force.

Before a build, absent cold-cache modules require no repair. After a build,
`--require-complete` requires an artifact and valid source trace for **every**
module in the current root source closure. A missing, unreadable, differently
resolved or differently imported module makes the job fail; repair removes
only that module's generated library/IR outputs. An existing module with a
changed body but unchanged imports is invalidated when its source trace hash
is old. These checks verify source-input and import-closure consistency; they
do not independently re-elaborate a proof body to prove that an arbitrarily
fabricated current-input trace corresponds to those bytes. The normal pinned
compiler build and the transitive axiom audit remain mandatory.

The workflow now separates compilation from auditing: repair, build, require
the complete current source closure, then run the pinned official audit with
the unchanged standard three-axiom allowlist. Reading the exact pinned
lean-action `action.yml` and `scripts/run_axiom_audit.sh` confirmed that the
audit script itself also invokes `lake build`, even with action `build: false`.
A final complete-closure check therefore follows that action as well.

Focused verification:

- The untouched independent witness is rejected with exit 1 specifically
  because the root's compiled imports differ from its current source header;
  all other current modules remain accepted. Its source and outputs were not
  repaired or rebuilt during this read-only verification.
- A controlled changed-child fixture added a new AgeAP import and a public
  declaration to `CCO.Examples`, retained the old valid output descriptors and
  old compiled bytes, and updated only the source-input hash to the current
  source. The old guard passed all 33 parts; the new guard rejected exactly
  `CCO/Examples.trace` for a compiled-import mismatch. Repair removed only its
  eight generated outputs and preserved the other children. The subsequent
  ordinary build completed 776 jobs; actual `import CCO` exposed both AgeAP
  and the new child declaration, and the official audit counted 655
  declarations (654 AgeAP base plus the new declaration), all allowed.
  The final guard accepted all 33 current modules and their olean parts.
- Five focused unit tests cover consistent-descriptor stale root/child headers,
  changed-body source inputs, cold versus required-complete closure, moved
  worktree prefixes/import flags, and audit-path shadowing. All 58 tests pass
  on this infrastructure source base. The guard also accepted all 158
  source modules and olean parts in the independently fresh B003 checkout
  `4efc0b3f4d8bd1197c3fd4dad3154901ae446e7a`.

The initiating cause of the observed stale-output snapshot remains unproved.
No claim is made that CAS, source hashing, the pinned compiler, or the copy
operation itself caused it. A separate fresh copy followed by ordinary build
and passive file-operation logging produced correct new outputs; ptrace-based
tracing was unavailable in this environment. Neither that successful build
nor a same-tree warm build is represented as explaining the preserved
failure. Remote workflow execution and review of the final integration head
are still required before deployment.

The independent combined RAW review exposed legitimate symlinked child
artifacts: the logical current-worktree path and its shared target identify
the same artifact. The audit-resolution comparison now resolves **both** paths.
A real-filesystem symlink regression accepts the logical path and its same
target alias, while rejecting a genuinely different artifact. All 59 tests
pass; the read-only complete check accepts all 317 modules/parts at reviewed
combined head `f01319ed98795f1e68b68a218a95c47459c8b2ab`, and still rejects the
unchanged original AgeAP witness for the root compiled-import mismatch.

## Directory aliases and one bounded clean-build fallback

A second independent control demonstrated an actual byte-check omission:
with the nested `CCO/StrongExact` output directory aliased to another
location, the old recursive scan checked only 33 olean parts even though
canonical metadata followed all 158 current source modules. Appending one
byte to the aliased Examples olean was then accepted. This is distinct from
the previously fixed equality comparison for individual file symlinks.

The guard now obtains canonical source metadata first and adds every exact
source-reachable trace path to the descriptor/byte check. It does not enable
recursive symlink following. The independent real fixture, including a
nested directory alias and a self-loop inside its target, now checks all
158 parts and rejects precisely the changed Examples descriptor. Normal
valid directory and individual-file aliases remain accepted.

Partial invalidation also checks both library and IR parent directories.
Unlinking a child through an aliased directory would mutate the external
target, so that case discards only this build's generated CCO namespace
instead, without traversing the aliases. Ordinary module invalidation stays
selective. Real filesystem tests cover both library and IR aliases; their
external output files survive repair. The common discard helper preserves
all sources, packages and non-CCO build outputs, including sentinels, and
unlinks directory symlinks without following them.

The independent preserved AgeAP repair copy confirmed a recovery limit:
removing one root module's eight outputs and then running a normal 776-job
build could still leave the old root, with AgeAP unavailable. The complete
new guard rejected it again before any successful audit. Disabling Lake's
artifact cache and rehashing is not claimed to universally repair that case
or to identify its initiating cause. A separate successful bounded variant
also exists; those observations must not be conflated.

The workflow now uses `LAKE_ARTIFACT_CACHE=false` and explicit
`lake --rehash build`, while retaining the GitHub project artifact archive
and targeted dependency cache. If, and only if, the complete post-build
check fails, it discards the generated CCO namespace, builds once from zero
CCO artifacts, and requires the complete check again before the official
audit. There is no recovery loop. The official audit and final complete
check remain mandatory. A failed clean rebuild or check fails the job.

The independent AgeAP clean fallback discarded ten generated namespace
files/trees, built 776 jobs, exposed AgeAP through `import CCO`, passed both
33-module/part checks around the official 654-declaration audit, and retained
the standard three-axiom allowlist. This is positive evidence for the bounded
clean fallback, separate from the failed incremental repair. The full local
infrastructure test suite has 63 passing tests on this source base.
If a namespace parent below the selected build boundary (`lib`, `lib/lean`
or `ir`) is itself aliased, clearing rejects before any deletion. A real
parent-alias test verifies external outputs remain untouched for all three
cases; namespace and deeper aliases are safely unlinked as described above.

Full accepted-source fallback validation used main
`4206ff772cc3ee334fe530b55dbb0afe8174dfd4` in a separate worktree, copying the
preserved combined snapshot whose root still exposed only B003's 157 direct
imports. The complete guard rejected its root header. The actual fallback
then discarded ten generated files/trees, verified zero remaining CCO
artifacts with sources and Mathlib packages intact, and completed a fresh
1211-job build. Both complete checks around the official audit accepted all
317 source modules and olean parts; the audit counted all 3657 declarations
with only the unchanged standard axioms. Actual `import CCO` checks exposed
AgeAP, the RAW general exact-ball Helly theorem, the actual canonical
quotient source properties, the STRONG genuine simple-path formula and
canonical exact-menu equivalence. This is the tested bounded recovery; no
universal repair or initiating-cause claim is inferred from it. Original
failure witnesses were not modified.
