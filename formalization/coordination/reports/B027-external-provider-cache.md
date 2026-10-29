# B027 external EPPA package and compiled dependency cache

The CCO encoding imports the public `AllThoseEPPA.MainTheorems` facade at
exact source pin `cd358cde844d5419fd43f30c441511927e09142f`, tree
`481ba0ca39c1074890582d85c7ae4ef20f107a20`. Its actual public unrestricted
coherent/faithful and restricted local-tree theorems are reused through the
B027 adapter; caching does not supply that mathematical bridge.

Lean remains 4.34.1. All nine existing resolved dependency name/URL/revision
triples are unchanged, including Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The only added manifest package
is `AllThoseEPPA`, whose source/configuration and proof provenance are
registered in `tools/external_provider.json`. The completed upstream
project was not changed.

## Actual roots and source/artifact checks

The facade reaches 269 upstream source modules and 35 Mathlib roots. It
does not import the whole 499-module upstream root and its applications.
The 151 CCO Mathlib roots at the receiving base and these 35 roots have a
163-root union. Later CCO consumers may add genuinely new roots; the list
is discovered from actual source headers rather than fixed at 163.

CI materializes the exact manifest first using `lake env true`, then checks
the provider pin/tree, toolchain, provider configuration hashes and shared
resolved pins before choosing a dependency cache key. The Mathlib walker
traverses both CCO source edges and the explicitly registered pinned
provider. It does not pass an unrecognized `AllThoseEPPA` namespace to the
Mathlib cache tool. Broad `Mathlib`/`Mathlib.Tactic` roots remain rejected.

The separate provider guard checks the complete 269-module facade closure:
actual source bytes against the pinned Git blobs (also catching
assume-unchanged source flags), parsed source and actual compiled import
headers/flags, Lake source-input hashes, all recorded olean output
descriptors/bytes and actual audit search-path resolution. Missing artifacts
are permitted only in a prebuild cold-cache check. An inconsistent cached
provider output is invalidated inside its private generated namespace and
rebuilt from the pinned source; a source/pin/configuration mismatch fails.
Aliases cannot cause repair to delete shared dependency outputs.

The default two-argument CCO metadata helper and CCO guard are preserved.
Provider diagnostics begin `External provider cache consistent`; they never
use `Project cache consistent`, which remains the CCO-only evidence prefix.
The complete CCO guards and official transitive standard-three axiom audit
remain in place before and after audit. The provider is also checked before
and after that audit.

## Cache identity and evidence

The provider cache stores only
`.lake/packages/AllThoseEPPA/.lake/build`, including traces and needed
native artifacts. Its exact key binds the provider source commit/tree,
facade root, OS/architecture, provider registration and both projects'
toolchain/manifest/Lake configuration hashes. It excludes the changing CCO
commit and CCO theorem source. There is no cross-configuration fallback.
The independent CCO incremental cache keeps its conservative existing key.
Its first new-manifest bootstrap may therefore compile earlier CCO modules.

Before B027 implementation, one local cold facade build passed 1,330 jobs
in 209.617 seconds and produced exactly 269 provider oleans. The same warm
target passed in 2.260 seconds: every olean SHA-256 and nanosecond timestamp
was unchanged, with no provider recompilation. The complete provider build
occupied 196,369,597 bytes, excluding shared Mathlib/dependency outputs.
These local measurements demonstrate reuse; CI runner timings may differ.
The copied artifacts were also tested from the receiving CCO dependency
layout: the facade target passed in 1.326 seconds with all 269 olean hashes
and timestamps unchanged and zero upstream modules rebuilt. The default
CCO guard still reported 894 artifact/source modules, while the separate
provider guard reported 269/269. The full Python suite passed 121 tests,
including 13 new provider test methods for pin/configuration changes,
hidden source changes, stale compiled headers, artifact bytes, input traces,
search-path shadowing, closure completeness and safe private invalidation.

The checked exact upstream CI is
https://github.com/shulda/lean_all_those_eppa_classes/actions/runs/39040857833
(job 117420066387): 1,886 build jobs and 4,350 `AllThoseEPPA` declarations
audited with the official auditor at
`46024e005996495c65ef609368e11ab39c4222e3`, allowing only `propext`,
`Classical.choice`, `Quot.sound`. A later cancelled run at the same source
is not used as green evidence. No upstream release or uploaded compiled
artifact existed, and the upstream workflow did not cache project outputs.
The upstream full audit was not repeated locally. CCO's transitive audit
still checks the axiom dependencies of every imported theorem it uses.

GitHub scopes PR-created caches to that PR's merge ref, so the first PR
cache cannot seed main or a sibling PR. The first receiving PR and its
first main push may both cold-build this dependency. Once a main-scoped
fixed-key cache exists, later CCO changes can reuse it naturally. No extra
CI push is required merely to demonstrate a warm cache.
Reference: https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching

## Local worktree preparation

After seeding an isolated CCO build and applying the exact new manifest,
run the following BEFORE any Lake command in that worktree:

```sh
python3 tools/prepare_eppa_worktree.py --project . \
  --provider-seed /path/to/runtime/external/all-those-eppa \
  --dependency-packages /path/to/runtime/packages
```

The helper verifies all nine shared dependency commits and the provider
seed, replaces only that worktree's package alias with a physical overlay,
creates a private detached provider Git worktree and copies the compiled
facade outputs. Each author has separate mutable provider build outputs;
neither the shared runtime package directory nor another author's build
is modified. These conveniences do not bypass final source/artifact checks,
independent review, exact-head CI or resulting-main CI.
