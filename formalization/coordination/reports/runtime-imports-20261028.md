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
that changed workflow passes CI. Python tests: all 48 pass on this branch;
workflow YAML syntax and retained audit settings were checked locally.
