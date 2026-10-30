# Precompiled external dependencies for the receiving Lean project

> Receiving context: this is the historical preparation engineering plan from
> `dc5fa9eafc2954909d15f3d18986d04fc8967513`. The
> [B037–B042 release record](coordination/releases/B037-B042/README.md),
> public protocol **3** and live STATE govern current work. Historical
> pending-provider counts are superseded by accepted B027 for HKN;
> B037 keeps its three HN binding obligations and forest work remains deferred.
> Existing receiving cache/audit policy and toolchain pins are unchanged.

Preparation note, 28 October 2026. This answers the user's request about
avoiding repeated HN/HKN verification during CCO work. It is a concrete
receiving implementation plan; no public CI, toolchain or acceptance
policy has been changed by this private preparation.

## Recommended build path

Use compiled dependency artifacts. Ordinary Lake builds use saved input
traces to skip unchanged outputs; compiled modules are imported from
`.olean` files. Cache the COMPLETE dependency build, including traces and
needed native libraries, rather than manually copying a single `.olean`.

1. Choose the receiving project's compatible Lean toolchain and pin the
   provider and every transitive dependency/Mathlib revision in the manifest.
   Build and perform the receiving protocol's provider/API/axiom checks for
   that configuration once. A published theorem without an implemented
   Lean declaration cannot be converted into an artifact by caching.
2. Store the resulting dependency build outputs as immutable CI cache or
   build artifacts. A suitable key is the toolchain, OS/architecture,
   exact provider/transitive manifest pins and relevant build configuration.
   Do NOT put the changing CCO commit in this DEPENDENCY key: otherwise
   every new CCO batch misses the same reusable provider build.
3. On subsequent CCO jobs, restore those artifacts and run normal Lake
   build/checks for the CCO targets and adapters. Lake still validates
   input traces and builds changed modules and necessary dependents.
   A cache miss or changed dependency configuration rebuilds the relevant
   dependency outputs rather than pretending the cache is current.

For the current workspace layout this normally means retaining the
provider's entire `.lake/build` output directory under its Lake package,
plus the corresponding transitive build outputs. The receiving team
should use its actual package paths and the chosen Lake version's artifact
layout. A separate layer can cache CCO outputs; it need not invalidate
the fixed external-library layer.

## Existing pins and the toolchain constraint

These are the references recorded in the preparation, not a claim about
the current active Work branch's selected toolchain:

| Input | Existing reference | Recorded Lean |
|---|---|---|
| HKN 1.1/1.2 | `shulda/lean_all_those_eppa_classes` at `cd358cde844d5419fd43f30c441511927e09142f` | `v4.34.1` |
| HN 2.19 | `janhubicka/partite-construction` at `918732dcff88fd1ab9be69f70e4f1d66385106e3` | `v4.35.0-rc3` |
| HN 2.6/2.11 | Exact receiving Lean declarations not yet verified | Pending |
| Factorization forest | `ReemMelamed/algebraic-automata` at `0acb244aaa913c32eeeff48e939cb5df469a3f70`, Mathlib `2a885768dae569d938bb9ff3474da6a8753bb90a` | `v4.35.0-rc3` |

Build products are not interchangeable across Lean toolchains. Before
using these implemented providers in ONE CCO workspace, select a compatible
toolchain/dependency set and port/rebuild the affected provider once as
needed. A green old pin is useful provenance, not a binary compatibility
promise. Caching does not discharge any of the six pending external-to-CCO
representation/statement bindings.

Import the narrow provider module actually needed by an adapter. For
the identified HN entry that is
`PartiteConstruction.Ramsey.AllThosePartialFiniteModels`; the recorded HKN
declarations are in `AllThoseEPPA.MainTheorems`. The forest theorem needs
`AlgebraicAutomata.FactorizationForest.Tree`; its separate infinitary
development is unnecessary. See [the pinned forest work order](https://github.com/shulda/cycle_constrainedness/blob/dc5fa9eafc2954909d15f3d18986d04fc8967513/cco-symmetric-eppa/papers/consolidated_working/formalization/FACTORIZATION_FOREST_PROVIDER.md).
Avoid adding a root import
that unnecessarily brings in an entire development. Transitive imports
remain real dependencies, even when their artifacts are cached.

## Ordinary build versus explicit proof replay

An incremental build and a fresh kernel replay are different operations.
`leanchecker --fresh` replays the selected module's declarations and
imported environment; restoring `.olean` files does not remove that cost.
Without `--fresh`, the checker can check selected modules over their
imported environment. These modes exist in both recorded Lean versions.

A reasonable receiving design is a full external-provider audit for each
new pin/configuration, retained as provenance, with cached dependencies
and the required checks of new CCO/adapter declarations on ordinary jobs.
Any currently mandatory fresh-replay or integration check remains in
force until that team's normal protocol review changes its scope. This
note does not disable checks or treat build success as the missing binding.

For distributing providers later, Lake also supports GitHub release build
archives (`preferReleaseBuild`) when matching upstream artifacts exist.
Ordinary CI caching is sufficient to start; no custom cache service or
new paid workflow is required by this plan. Newer fine-grained Lake cache
commands are version-dependent/experimental, so their exact use belongs
to the receiving implementation on its chosen toolchain.

## Verification of the cache setup

The receiving implementation should demonstrate a cold successful build,
a warm job reusing unchanged provider outputs, and invalidation after a
provider/toolchain/manifest change. Confirm the build log skips external
re-elaboration while still rebuilding a deliberately changed CCO adapter.
Keep provider audit provenance separate from ordinary cache-hit evidence.
This is the engineering acceptance criterion, not a mathematical proof test.

## Receiving reminder: factorization-forest licensing

Before importing or porting the forest provider, follow the explicit
[licensing and attribution gate in its updated work order](https://github.com/shulda/cycle_constrainedness/blob/30abcca888c0348f6b1ce5a32581b9250e5f7ae5/cco-symmetric-eppa/papers/consolidated_working/formalization/FACTORIZATION_FOREST_PROVIDER.md).
Retain the exact upstream Apache-2.0 LICENSE and Re'em Melamed-Katz's
copyright/authorship, preserve applicable notices and any NOTICE attribution,
and put prominent change notices in each modified upstream file. Record
original source and receiving patches separately. Include required license
and notices when distributing compiled provider artifacts as well as source.
The CCO adapter must identify upstream proof authorship separately from the
receiving application. This reminder adds no mathematical assumption or
provider installation and does not change the source/toolchain/cache pins.

Primary documentation consulted:

- [Lake build traces, artifact caches and release builds](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/).
- [Lean proof validation and selective/fresh replay](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).
- [Lean 4.34.1 checker source](https://github.com/leanprover/lean4/blob/v4.34.1/src/LeanChecker.lean)
  and [Lean 4.35.0-rc3 checker source](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/LeanChecker.lean).

The mathematical batch `relational_completion` adds no external provider;
this cache note is ancillary and included in the deterministic handoff.
