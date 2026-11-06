# Runtime restoration — 6 November 2026

Actual runtime-only agent: `/root/runtime_cache_b`.
Private source clone `/workspace/scratch/e67502cd723c/work-runtime`, accepted main `1c6b21e63b0c8382ea13adaaeb5903440c59c334`.
No tracked source, policy, branch, manifest or toolchain changes/publication.

## Restored compiler and source dependencies

No lean/lake/elan or exact release archive was found in the usual global/runtime cache locations after scratch reset. Downloaded once from official exact release URL:
`https://github.com/leanprover/lean4/releases/download/v4.34.1/lean-4.34.1-linux.tar.zst`.

- Lean 4.34.1, release commit `5045d0056413266e57c625dcd7c365b10e377c52`.
- Lake 5.0.0-src+5045d00.
- Compiler directory `.runtime-tools/lean-4.34.1-linux/bin`.
- Standalone Init theorem compiled; actual axiom print: runtime_smoke depends on no axioms.
- Manifest SHA256 `740aed1eb25fe64004f1b860865c0c9c362080aef71e76d9bfe4697a779d4cb1`, unchanged.
- All ten git dependency sources fetched shallowly at exact manifest SHA and checked against actual HEAD. This avoids downloading old mathlib history; source tree and revision are identical to the pins.
- `lake env true` passed; git source diff remains empty.

## Mathlib cache and providers

Actual `tools/mathlib_cache_roots.py --include-provider --reject-broad` produced 236 narrow roots.
Downloaded and decompressed their 2282 transitive Mathlib cache files successfully. No concrete network failure occurred. No blanket Mathlib root was requested.

Both exact pinned provider facade builds completed successfully:

- EPPA: 1330-job build PASS; complete guard checks 269/269 current source modules at exact pin `cd358cde844d5419fd43f30c441511927e09142f`.
- Ramsey: 1182-job build PASS; complete guard checks 106/106 current source modules at exact subtree `374241ce3751715c90b12c0b071f36026819ad4a`.
- All runtime build sessions have finished. `.lake/packages` and `vendor/ramsey/.lake` are stable for independent copies into the three implementation worktrees.
- Root and all three implementers were notified of staged and final stable copy points. Runtime contains no CCO production outputs from sibling WIP branches and no whole accepted-main CCO prewarm.
- Logs: `.runtime-tools/eppa-build.log`, `ramsey-build.log`, `mathlib-cache-get.log`, `dependency-resolution.log`, `toolchain-download.log`, `axiom-audit-build.log`.


All builds use:
```bash
export PATH="$PWD/.runtime-tools/lean-4.34.1-linux/bin:$PATH"
export LAKE_RESTORE_ARTIFACTS=true
export LAKE_ARTIFACT_CACHE=false
lake env true
python3 tools/verify_external_provider.py --cache-key --os Linux --arch X64
python3 tools/verify_ramsey_provider.py --cache-key --os Linux --arch X64
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

No optional full accepted CCO cold prewarm was started. Stable dependency trees must be copied separately into each implementer's own `.lake` and vendor outputs; concurrent builders must not use this runtime's build directories.

## Compiled CI outputs availability check

The connector supports listing and downloading real Actions artifact ZIP archives. Queried these actual exact-green runs:

- accepted main:42114181673
- B053:42115110122
- B060:42115128451
- B062:42115145937

All four returned `artifacts: []`. Current `.github/workflows/lean.yml` uses actions/cache and no upload-artifact. Existing connected APIs expose no cache archive-download endpoint. No attempt was made to retrieve workflow secrets, cache service tokens or bypass input-hash guards. Coordinator is separately considering an ephemeral, guard-preserving artifact export workflow.

## Audit tool

Rebuilt dependency-free standard audit tool v0.1.2 at exact commit `46024e005996495c65ef609368e11ab39c4222e3` under `.runtime-tools/axiom-audit` with the pinned project compiler; build passed (6 jobs).

After full relevant project compilation and source guards, from that PRIVATE project root:
```bash
lake env /workspace/scratch/e67502cd723c/work-runtime/.runtime-tools/axiom-audit/.lake/build/bin/axiom-audit --root CCO --allow propext,Classical.choice,Quot.sound --json
```

At this pre-artifact checkpoint, no whole-CCO local build or transitive audit was claimed. The verified restoration below supersedes that runtime status; it does not imply mathematical completion, package review or acceptance.

## Private worktree setup

Copy only stable dependency outputs/sources, never share writable build directories:

```bash
# Run in each separately owned worktree, before its builder starts.
mkdir -p .lake vendor/ramsey
cp -a --reflink=auto /workspace/scratch/e67502cd723c/work-runtime/.lake/packages .lake/
cp -a --reflink=auto /workspace/scratch/e67502cd723c/work-runtime/vendor/ramsey/.lake vendor/ramsey/
export PATH="/workspace/scratch/e67502cd723c/work-runtime/.runtime-tools/lean-4.34.1-linux/bin:$PATH"
export LAKE_RESTORE_ARTIFACTS=true
export LAKE_ARTIFACT_CACHE=false
lake env true
# Then build only the relevant private source target and its actual consumers.
lake --rehash build +CCO.TargetModule
```

The final example target is a placeholder for the implementer's real module, not a repository declaration. Existing active builders must finish or be paused before merging cache copies into their own outputs. At this pre-artifact checkpoint no full local CCO axiom audit had yet run. See the completed verification below.

## Prepared verified CI recovery (historical checkpoint before artifact)

Read exact PR75 workflow at head `5c8410717cdd2ea640e5f2e9de4b6beec1bb5179`. Git comparison against this accepted runtime main shows differences only in `.github/workflows/lean.yml` and the export report/review; `CCO/`, `CCO.lean`, all three pins/configuration files, `tools/` and `vendor/` are byte-identical. This is a permissible build seed, not an accepted mathematical dependency.

Runtime-only helper `.runtime-tools/restore_verified_build.py` is syntax-checked and ready. It validates exactly three ZIP files (`build.tar.gz`, `checkout-sha.txt`, `input-sha256.txt`), the actual CI checkout SHA supplied from checkout logs, all four pinned/root SHA256 values, and every tar member/link target. It extracts into a fresh staging directory; `--restore` preserves old output trees and replaces only the three known build directories with rollback on move failure. Runtime has no active builder.

PR Actions checkout may be a synthetic merge SHA; do not assume it equals workflow run head SHA. Bind the actual checkout commit to inspected logs and verify its complete Lean/toolchain/provider source tree matches accepted main before invoking restore. Signed download URLs must not be included in reports or logs.

After actual successful CI and artifact download, use the real artifact filename and actual checkout SHA:

```bash
python3 .runtime-tools/restore_verified_build.py --zip ACTUAL_ZIP_PATH \
  --expected-checkout-sha ACTUAL_CI_CHECKOUT_SHA \
  --expected-runtime-head 1c6b21e63b0c8382ea13adaaeb5903440c59c334 \
  --stage .runtime-tools/restore-ACTUAL_RUN-ACTUAL_ATTEMPT --restore
python3 tools/verify_project_cache.py --require-complete
python3 tools/verify_external_provider.py --require-complete
python3 tools/verify_ramsey_provider.py --require-complete
lake --rehash build
python3 tools/verify_project_cache.py --require-complete
python3 tools/verify_external_provider.py --require-complete
python3 tools/verify_ramsey_provider.py --require-complete
lake env .runtime-tools/axiom-audit/.lake/build/bin/axiom-audit --root CCO --allow propext,Classical.choice,Quot.sound --json
```

Only after these checks may root CCO `.lake/build` be offered as a private-copy seed. Implementers must first stop their own builders and still run their own actual-source repair/rehash checks. No artifact has yet been restored at this report checkpoint.

## Completed verified CI recovery — 2026-11-06 07:13 UTC

**Stable runtime build snapshot:** `/workspace/scratch/e67502cd723c/work-runtime/.lake/build`.

No builder remains active in this runtime and its build trees will remain unchanged while private copies are made. The mathematical checkout remains accepted main `1c6b21e63b0c8382ea13adaaeb5903440c59c334`; tracked files are unchanged. The artifact export tooling branch is not treated as an accepted mathematical dependency.

### Provenance and bounded restore

- Own CI run `42171760411`, job `127740981590`, artifact `13481592728`; parent coordinator verified complete workflow success including upload and standard audit.
- Downloaded ZIP: `.runtime-tools/cco-verified-build-42171760411.zip`, 250,681,130 bytes, SHA256 `c73a0fec85133fe8d570d1b1d127eb7898f7d9560caffd9847d958b26fd4ddc0` (independently rechecked by restore helper).
- Actual CI checkout metadata: `07b5b1a5e3e44fb001e83e5cd9d81934fe2eb722`. Exact local `git diff --exit-code HEAD 07b5b1a5e3e44fb001e83e5cd9d81934fe2eb722 -- CCO CCO.lean lean-toolchain lake-manifest.json lakefile.toml tools vendor` passed before restoration. Parent and independent reader additionally bound its merge parents/full tree to the approved tooling-only export PR.
- ZIP contained exactly `build.tar.gz`, `checkout-sha.txt`, `input-sha256.txt`. All four CI input hashes matched local accepted inputs, as listed in `.runtime-tools/restore-42171760411-1/validated.json`.
- All 18,002 tar members and link targets passed bounded path/type/link validation and Python data-filter staging extraction; regular files total 2,330,411,739 bytes.
- Only `.lake/build`, `.lake/packages/AllThoseEPPA/.lake/build`, and `vendor/ramsey/.lake/build` were replaced. Previous EPPA/Ramsey outputs remain preserved under `.runtime-tools/restore-42171760411-1/backups/1` and `backups/2`; root project output did not previously exist. No other worktree was modified.

### Actual checks and outcomes

1. Before rehash, all `--require-complete` guards passed: project 1842/1842 source modules, EPPA 269/269 at exact pin `cd358cde844d5419fd43f30c441511927e09142f`, Ramsey 106/106 at exact subtree `374241ce3751715c90b12c0b071f36026819ad4a`.
2. `lake --rehash build` succeeded (4516 jobs). Log `.runtime-tools/restored-main-rehash-42171760411.log` shows replayed warnings and no reported newly Built jobs; this was a warm validation, not a cold accepted-main prewarm.
3. All three complete guards passed again after rehash with the same counts/pins.
4. Standard transitive axiom audit passed: `audited=30216`, `axiomsUsed=[propext, Classical.choice, Quot.sound]`, `ok=true`, `violations=[]`. Machine-readable result: `.runtime-tools/restored-main-audit-42171760411.json`.
5. Final complete project guard passed, 1842/1842. The verification shell completed exit 0. No guard bypass or repair was necessary in this accepted runtime.

Exact restore/verification commands:

```bash
python3 .runtime-tools/restore_verified_build.py \
  --zip .runtime-tools/cco-verified-build-42171760411.zip \
  --expected-checkout-sha 07b5b1a5e3e44fb001e83e5cd9d81934fe2eb722 \
  --expected-runtime-head 1c6b21e63b0c8382ea13adaaeb5903440c59c334 \
  --expected-zip-sha256 c73a0fec85133fe8d570d1b1d127eb7898f7d9560caffd9847d958b26fd4ddc0 \
  --stage .runtime-tools/restore-42171760411-1 --restore
set -euo pipefail
export PATH="$PWD/.runtime-tools/lean-4.34.1-linux/bin:$PATH"
export LAKE_RESTORE_ARTIFACTS=true
export LAKE_ARTIFACT_CACHE=false
python3 tools/verify_project_cache.py --require-complete
python3 tools/verify_external_provider.py --require-complete
python3 tools/verify_ramsey_provider.py --require-complete
lake --rehash build > .runtime-tools/restored-main-rehash-42171760411.log 2>&1
python3 tools/verify_project_cache.py --require-complete
python3 tools/verify_external_provider.py --require-complete
python3 tools/verify_ramsey_provider.py --require-complete
lake env "$PWD/.runtime-tools/axiom-audit/.lake/build/bin/axiom-audit" \
  --root CCO --allow propext,Classical.choice,Quot.sound --json \
  > .runtime-tools/restored-main-audit-42171760411.json
python3 tools/verify_project_cache.py --require-complete
```

All three implementers were notified that the accepted-main root build seed is stable. Each must stop its own builder before copying into its own `.lake/build`, then run its own actual-source `python3 tools/verify_project_cache.py --repair` and `lake --rehash build +ACTUAL_TARGET` (plus required consumers/root/audit for final scope). WIP additions and changed root imports are intentionally not certified by the accepted-main artifact and must be rebuilt. The runtime actor did not write into implementation worktrees or publish repository changes.
