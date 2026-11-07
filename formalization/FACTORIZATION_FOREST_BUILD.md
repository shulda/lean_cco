# Receiving finite factorization forest build

This receiving plumbing uses the already reviewed finite compatibility port at
`vendor/factorization-forest/`, with original formalization authorship attributed
to Re'em Melamed-Katz. Upstream remains
`ReemMelamed/algebraic-automata@0acb244aaa913c32eeeff48e939cb5df469a3f70`;
the complete receiving vendor subtree is
`ee892229b9f4be545bfce74d7b53ac9136616dc2`. No provider proof file, receiving
toolchain, dependency manifest or transitive dependency pin changes here.

The second receiving `lean_lib`, `AlgebraicAutomata`, reads this source
directory and builds exactly its fourteen inventoried modules. The glob makes
all fourteen actual imports buildable under Lake 4.34.1; the source guard
separately rejects added/missing sources and requires the actual Tree import
closure to equal the pinned inventory. Its library options preserve all five
original receiving options, including `autoImplicit=false`,
`relaxedAutoImplicit=false`, `weak.linter.mathlibStandardSet=true` and
`maxSynthPendingDepth=3`. The original standalone port remains unchanged.

`CCO.FactorizationForest.Provider` imports only the narrow Tree root and exports
`CCO.FactorizationForest.classical_bound`, applying the unchanged global theorem.
Its hypotheses are arbitrary alphabet `A`, `[Semigroup S] [Fintype S]
[Nonempty S]`, total evaluation, multiplicativity on concatenations of two
nonempty words, and a nonempty input word. The result preserves literal yield,
`IsRamsey` and height at most `3 * card S - 1`. `CCO.lean` directly imports the
facade. There is no monoid/identity, finite-alphabet or empty-word law premise.

This does not construct B058's typed zero-completed semigroup or its nonempty
append law, convert the ordered tree to contiguous original intervals, discharge
nonzero subtree values, or complete the source bounded-obstruction instance.
Independent exact-head review, provider-aware GitHub CI and resulting-main
build/audits still govern integration and acceptance.

## Source and compiled cache checks

`tools/factorization_forest_provider.json` separately registers the exact
upstream commit, immutable receiving subtree, original configuration hashes,
all eleven existing receiving manifest entries, the compiler commit and the
791-declaration module-origin audit count. The source guard checks every
tracked vendor blob against its current bytes, even if index flags conceal
an edit. It also verifies the complete fourteen-module actual import closure,
pinned provenance, every ported source hash, full license and every
original/modification notice.

The compiled guard reuses the existing receiving Lean parser, module-header
reader and pinned Lake byte-hash helper. It checks all fourteen source hashes,
compiled import headers and search-path resolution, all 42 olean partitions,
plus all 56 C/IR/editor outputs against their real trace descriptors. Real
trace captions must bind the exact receiving compiler, original compiler
options, module identity and receiving package. Extra compiled modules and
artifact aliases are rejected. `--repair` clears only the owned provider
namespace and its distribution; CCO and other provider outputs survive.

The dependency key binds platform/architecture, original pin, receiving port,
toolchain, source/configuration/transitive pins and guards. It excludes the
changing CCO commit. The separate provider cache contains:

- `.lake/build/lib/lean/AlgebraicAutomata`;
- `.lake/build/ir/AlgebraicAutomata`;
- `.lake/factorization-forest-distribution`.

The last directory contains the **entire pinned source distribution**: the
full Apache-2.0 LICENSE, all original copyright/author headers, all per-file
modification notices, provenance, compatibility patch, original configuration
and source review evidence. This preserves attribution with compiled cache
redistribution. Missing, aliased or changed distribution files invalidate the
cache. The CCO incremental cache now selects only `CCO` namespace artifacts,
so its restore cannot overwrite the independently checked forest cache.

The actual import traversal follows `AlgebraicAutomata` edges and discovers all
sixteen specific Mathlib roots from the finite closure, then merges them with
the actual project/other-provider roots. It does not use a broad Mathlib import.

## Reproducible receiving checks

With the pinned receiving compiler/Lake in PATH and exact dependencies ready:

```sh
python3 tools/verify_factorization_forest_provider.py --cache-key
python3 tools/mathlib_cache_roots.py --include-provider --reject-broad
python3 tools/verify_factorization_forest_provider.py --repair
lake --rehash build +AlgebraicAutomata.FactorizationForest.Tree
python3 tools/verify_factorization_forest_provider.py --prepare-distribution
python3 tools/verify_factorization_forest_provider.py --require-complete
lake --rehash build
python3 tools/verify_project_cache.py --require-complete
python3 tools/verify_external_provider.py --require-complete
python3 tools/verify_ramsey_provider.py --require-complete
```

The existing pinned lean-action continues its transitive `CCO` audit. The
additional provider audit uses the **same real tool pin**, axiom-audit v0.1.2
commit `46024e005996495c65ef609368e11ab39c4222e3`, compiled with the unchanged
receiving toolchain. No invented action input or audit option is used:

```sh
python3 tools/audit_factorization_forest.py --audit /absolute/path/to/axiom-audit
```

The helper first requires complete provider guards, then invokes the actual
CLI with `--root AlgebraicAutomata --modules
AlgebraicAutomata.FactorizationForest.Tree --allow
propext,Classical.choice,Quot.sound --json`. It requires exactly 791 audited
declarations and no violations. The tool selects defining-module origin, so
unnamespaced global declarations are included. Both audits are followed by
all complete guards in CI. No fresh kernel replay is claimed by these checks.

## Verified-build export and restore

The actual CI exporter now calls `tools/package_verified_build.py` after the
full build, both audits and final complete guards. The existing unique-run,
one-day recovery artifact policy is unchanged. Its tar contains the three
existing private build roots **and** the complete licensed provider distribution
above. The ZIP wrapper still contains exactly `checkout-sha.txt`,
`input-sha256.txt` and `build.tar.gz`.

`tools/restore_verified_build.py` extends the actual runtime recovery helper
with that distribution. Supply the exact successful run checkout, expected
current project head and optionally the downloaded artifact SHA256. It checks
all four pinned/root input hashes and a clean tracked source state; validates
every ZIP/tar path, duplicate, type and link; extracts into a fresh private
stage directly under the receiving `.lake`; and verifies every source/license/
provenance distribution byte before changing any output tree. Physical private
destinations are preflighted and previous outputs retained for rollback.

```sh
python3 tools/restore_verified_build.py \
  --zip /absolute/path/to/verified-build.zip \
  --expected-checkout-sha EXACT_SUCCESSFUL_CI_CHECKOUT \
  --expected-project-head EXACT_CURRENT_PROJECT_HEAD \
  --stage /absolute/path/to/own/worktree/.lake/recovery-stage \
  --restore
```

An archived build remains a compilation seed. Use an independently owned
worktree with no concurrent build writer, then run source/cache repair,
`lake --rehash build`, every complete guard and both actual audits. Restoration
does not grant acceptance or replace current-source proof validation.

The regression fixtures exercise the actual exporter and restore CLI, including
full license/per-file notices, exact input checks, removal of a binary license,
path traversal, forbidden source members, escaping links, source/namespace
aliases, concealed source changes, original compiler options, native output
presence, exact import roots, dependency-key stability and complete audit count.
