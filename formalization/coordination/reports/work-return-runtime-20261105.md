# Work runtime dependency cache checkpoint — 5 November 2026

Actual runtime-only setup actor: `/root/runtime_cache_b`.
Root publisher/coordinator instructed this agent to prepare private caches and then stop optional whole-main prewarming to reserve resources for three meaningful targeted builds. This report claims no package implementation, source certification, independent approval or complete project audit.

Source clone: `/workspace/scratch/e67502cd723c/work-runtime`.
Exact source HEAD remains `6c11e37510dbbb819137cb956cf53c2c1a9e5b03`.
No tracked source, policy, manifest, toolchain or lakefile changes; no publication.

## Compiler and manifest

- Lean 4.34.1, release commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lake 5.0.0-src+5045d00.
- Compiler path: `.runtime-tools/lean-4.34.1-linux/bin`.
- Manifest SHA256 `740aed1eb25fe64004f1b860865c0c9c362080aef71e76d9bfe4697a779d4cb1`.
- All ten git dependency HEADs checked again against actual manifest revisions: all match.
- Earlier small `CCO.FullCode.Basic` build and repeated incremental rehash both passed (669 jobs); standalone Init proof compiler smoke passed. See `RUNTIME_SETUP.md`.

## Completed dependency preparation

```bash
export PATH="$PWD/.runtime-tools/lean-4.34.1-linux/bin:$PATH"
export LAKE_RESTORE_ARTIFACTS=true
export LAKE_ARTIFACT_CACHE=false
python3 tools/mathlib_cache_roots.py --include-provider --reject-broad > .runtime-tools/mathlib-roots.txt
mapfile -t roots < .runtime-tools/mathlib-roots.txt
MATHLIB_CACHE_DIR="$PWD/.runtime-tools/mathlib-cache" lake exe cache get "${roots[@]}"
python3 tools/verify_external_provider.py --repair
lake --rehash build +AllThoseEPPA.MainTheorems
python3 tools/verify_external_provider.py --require-complete
python3 tools/verify_ramsey_provider.py --repair
lake --rehash build +CCORamsey
python3 tools/verify_ramsey_provider.py --require-complete
```

- Actual narrow import discovery: 236 external roots; no broad Mathlib/Mathlib.Tactic root.
- Cache download passed without network failure: 1629 additional transitive files, 2282 total decompressed (653 from initial smoke target).
- EPPA facade build passed: 1330 jobs, all 269 current source olean modules, exact pin `cd358cde844d5419fd43f30c441511927e09142f`.
- Ramsey facade build passed: 1182 jobs, all 106 current source olean modules, exact source subtree `374241ce3751715c90b12c0b071f36026819ad4a`.
- Both `--require-complete` guards passed again after optional main build stopped.
- `.lake/packages` and `vendor/ramsey/.lake` are stable and were offered for COPY/reflink into the three private worktrees. No shared writable dependency/build symlinks were requested.

Logs: `full-root-cache.log`, `eppa-build.log`, `ramsey-build.log`.

## Deliberately partial accepted-main prewarm

Started `taskset -c 0-3 lake --rehash build` in this private runtime after both facades passed. Root then explicitly instructed stopping this optional cold whole-project build because four simultaneous cold closures were duplicating work and causing contention on 9 CPUs / 9.7 GiB RAM.

Sent Ctrl-C to only own unified-exec session 50448. Shell exited 130. All completed artifacts preserved; no cache reset. Final local root count: 22 CCO olean modules out of 1842 current source modules. Readonly `python3 tools/verify_project_cache.py` passed for this partial cache; it does NOT claim `--require-complete`.

Root `.lake/build` now has no active writer; log stopped at local timestamp `2026-11-05 22:29:47 +0100`. All three implementers notified. Their existing private targeted builds had already surpassed this partial source cache, so no redundant merge-copy was needed.

Whole accepted CCO closure and whole CCO transitive audit were NOT completed in this local runtime. Do not report them as passed. Existing remote accepted-main CI/audit remain separate evidence inspected by the coordinator.

A readonly `lake --no-build build +AllThoseEPPA.MainTheorems` probe taken during the provider build returned exit 3 because one then-pending target was not yet built; the actual subsequent full facade build and all final guards passed. This was not a source proof failure.

## Audit tool ready, not yet run on whole CCO

The exact standard audit tool `leanprover-community/axiom-audit` v0.1.2 at commit `46024e005996495c65ef609368e11ab39c4222e3` was cloned under `.runtime-tools/axiom-audit` and built with the project compiler (6 jobs, pass). It is separate from project source/manifest and imports only Lean core.

After a complete project build and guards, run from the relevant PRIVATE project root:

```bash
lake env /workspace/scratch/e67502cd723c/work-runtime/.runtime-tools/axiom-audit/.lake/build/bin/axiom-audit --root CCO --allow propext,Classical.choice,Quot.sound --json
```

No whole-CCO local audit output exists yet. Runtime setup sessions are finished; caches remain available for the coordinator and independently owned worktrees.
