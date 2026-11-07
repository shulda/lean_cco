# Independent upstream inventory — factorization forest provider preparation

Actual inventory agent: `/root/b053_resume/forest_inventory`. Date: 6 November 2026.
This is a read-only provenance/import/license/API inventory for advance provider preparation. It is not a B058 claim, implementation review, compiled audit or acceptance.

Upstream: `https://github.com/ReemMelamed/algebraic-automata`, exact detached commit `0acb244aaa913c32eeeff48e939cb5df469a3f70`; clean checkout verified. Work order read in full: `formalization/FACTORIZATION_FOREST_PROVIDER.md` at receiving base `68faa81d1d2af95ad58f6937afdd1afd97bb49ad`.

## Narrow exact source closure

Following both `public import` and ordinary `import` from `AlgebraicAutomata.FactorizationForest.Tree` yields exactly **14 Lean source files, 4,079 lines, 184,508 UTF-8 bytes**. The counts concern the original unmodified provider closure. No project umbrella, application, `Infinitary.lean` or `TreeToSplit.lean` is needed. Upstream uses `module` and `@[expose] public section`; an ordinary-import-only scanner would miss this closure.

| Upstream path | Git blob SHA-1 | SHA-256 | Lines |
|---|---|---|---:|
| `AlgebraicAutomata/FactorizationForest/Basic.lean` | `ef7a2e8b5f7be0e3627463616354c154f61ba4cb` | `c4b0f3fa03053da03b8d3306083aaa8d237fe7032e81e2747e0ae9a983d7f55b` | 479 |
| `AlgebraicAutomata/FactorizationForest/Combine.lean` | `350fb96afff81cf33ab19731ae0f091a25753b1e` | `7c8b19b80019c14c0ac0ffe2842082343d0e384ede74522138970e3f40a836b4` | 708 |
| `AlgebraicAutomata/FactorizationForest/Irregular.lean` | `b77fb07a593e8660b8326c8dcf236be6d5938acd` | `bce9d3af27c47d1a7368f565c38a9b8e4542108bdc542f03aeb2efa4f48cbb45` | 190 |
| `AlgebraicAutomata/FactorizationForest/Regular.lean` | `e5e2d307cd344563bf0742a02094b265455e3fb9` | `07afc09f4809b3a3624626504b96110f2179699df79fd05ec455c879136e03d3` | 525 |
| `AlgebraicAutomata/FactorizationForest/Split.lean` | `f395a92a90ef0d004b3c095d95197994b02b8ec2` | `e3255e8b803729f129a6a52745b8856311c635abcd94caea4669ab7e5e13a498` | 108 |
| `AlgebraicAutomata/FactorizationForest/Tree.lean` | `91d4d2759364a7a592e1a93abcc0b8ab2811ed37` | `48e1a35b426118b17049acda8eb5c72ae1151ddba1f2a04a461e007e4410aee8` | 660 |
| `AlgebraicAutomata/ForMathlib/Algebra/Group/Opposite.lean` | `c8b27562d0017083c5c58950c165f843062a6ef7` | `f57f98c22804b9088c91e47ad150a2f5d3eff86add3c407cc2940283e44f09c2` | 27 |
| `AlgebraicAutomata/ForMathlib/Data/List/SemigroupProd.lean` | `4d30252e80c13eb701f5056a8ee790fc25020062` | `d8c2c98ed6558e53dee786e463991967352dde1326ab60bde6e616f9e4cd63e7` | 122 |
| `AlgebraicAutomata/ForMathlib/Data/List/Slice.lean` | `6fe7347ab7de313e9a5d15302228d77e92bba7c8` | `716e181a7d8731b960f1d8836c78909f03165ffc4e8cb33e51ae13286001a232` | 61 |
| `AlgebraicAutomata/GreensRelations/Basic.lean` | `1d0114cafdda8ff368c9c99672c5166d3416cdf0` | `1faaf167f7b3c61d765aa77c6c28dcb61093109e5a1b3ab0a34a30597e1c32f6` | 511 |
| `AlgebraicAutomata/GreensRelations/Finite.lean` | `0c4e8a78345ebbac0f69d012ad8d76d494c14014` | `620c7f7f906e18a27486499cebee59f8c203bc0eb9f21b2deac7681b0ff9427a` | 246 |
| `AlgebraicAutomata/GreensRelations/Green.lean` | `7b68773a5b0eb955e639c8dd657ee5c0921a8ea4` | `3c6666ff900ed5127634b7704d2b4e1a8af3d19d8de82cf4da35d5e03d79e137` | 156 |
| `AlgebraicAutomata/GreensRelations/MulSeq.lean` | `175426cd3d29456750d7d839b222b70f0c58a508` | `051be8987d4861f3ff430342a78798b0231a5cfcd362dd0b5851ceb0bfb829d9` | 191 |
| `AlgebraicAutomata/GreensRelations/Order.lean` | `1ed617e6d51cdbd10f50ae9abcfe2413e927c285` | `bdc30e92b13c698e5767046058982254fa01b792c97c8d18e9486e3d62ba2808` | 95 |

The exact original internal import edges and direct external imports are recorded below; no source files were changed by this agent.

```json
{
  "closure": [
    {
      "path": "AlgebraicAutomata/FactorizationForest/Tree.lean",
      "git_blob": "91d4d2759364a7a592e1a93abcc0b8ab2811ed37",
      "sha256": "48e1a35b426118b17049acda8eb5c72ae1151ddba1f2a04a461e007e4410aee8",
      "bytes": 29958,
      "lines": 660,
      "imports": [
        "Mathlib.Algebra.Group.Idempotent",
        "Mathlib.Data.Fintype.Basic",
        "Mathlib.Data.Finset.Max",
        "AlgebraicAutomata.FactorizationForest.Split",
        "AlgebraicAutomata.ForMathlib.Data.List.SemigroupProd",
        "AlgebraicAutomata.ForMathlib.Data.List.Slice"
      ]
    },
    {
      "path": "AlgebraicAutomata/ForMathlib/Data/List/Slice.lean",
      "git_blob": "6fe7347ab7de313e9a5d15302228d77e92bba7c8",
      "sha256": "716e181a7d8731b960f1d8836c78909f03165ffc4e8cb33e51ae13286001a232",
      "bytes": 2314,
      "lines": 61,
      "imports": [
        "Mathlib.Data.List.Basic"
      ]
    },
    {
      "path": "AlgebraicAutomata/ForMathlib/Data/List/SemigroupProd.lean",
      "git_blob": "4d30252e80c13eb701f5056a8ee790fc25020062",
      "sha256": "d8c2c98ed6558e53dee786e463991967352dde1326ab60bde6e616f9e4cd63e7",
      "bytes": 4358,
      "lines": 122,
      "imports": [
        "Mathlib.Algebra.Group.Subsemigroup.Basic",
        "Mathlib.Data.List.Basic"
      ]
    },
    {
      "path": "AlgebraicAutomata/FactorizationForest/Split.lean",
      "git_blob": "f395a92a90ef0d004b3c095d95197994b02b8ec2",
      "sha256": "e3255e8b803729f129a6a52745b8856311c635abcd94caea4669ab7e5e13a498",
      "bytes": 4098,
      "lines": 108,
      "imports": [
        "AlgebraicAutomata.FactorizationForest.Regular",
        "AlgebraicAutomata.FactorizationForest.Irregular"
      ]
    },
    {
      "path": "AlgebraicAutomata/FactorizationForest/Irregular.lean",
      "git_blob": "b77fb07a593e8660b8326c8dcf236be6d5938acd",
      "sha256": "bce9d3af27c47d1a7368f565c38a9b8e4542108bdc542f03aeb2efa4f48cbb45",
      "bytes": 9024,
      "lines": 190,
      "imports": [
        "AlgebraicAutomata.FactorizationForest.Combine"
      ]
    },
    {
      "path": "AlgebraicAutomata/FactorizationForest/Combine.lean",
      "git_blob": "350fb96afff81cf33ab19731ae0f091a25753b1e",
      "sha256": "7c8b19b80019c14c0ac0ffe2842082343d0e384ede74522138970e3f40a836b4",
      "bytes": 33953,
      "lines": 708,
      "imports": [
        "Mathlib.Data.Fintype.Card",
        "Mathlib.Data.Finset.Max",
        "AlgebraicAutomata.FactorizationForest.Basic"
      ]
    },
    {
      "path": "AlgebraicAutomata/FactorizationForest/Basic.lean",
      "git_blob": "ef7a2e8b5f7be0e3627463616354c154f61ba4cb",
      "sha256": "c4b0f3fa03053da03b8d3306083aaa8d237fe7032e81e2747e0ae9a983d7f55b",
      "bytes": 21130,
      "lines": 479,
      "imports": [
        "Mathlib.Data.Finset.Max",
        "Mathlib.Data.Fintype.EquivFin",
        "AlgebraicAutomata.GreensRelations.Order",
        "AlgebraicAutomata.ForMathlib.Data.List.Slice"
      ]
    },
    {
      "path": "AlgebraicAutomata/GreensRelations/Order.lean",
      "git_blob": "1ed617e6d51cdbd10f50ae9abcfe2413e927c285",
      "sha256": "bdc30e92b13c698e5767046058982254fa01b792c97c8d18e9486e3d62ba2808",
      "bytes": 3296,
      "lines": 95,
      "imports": [
        "AlgebraicAutomata.GreensRelations.Finite"
      ]
    },
    {
      "path": "AlgebraicAutomata/GreensRelations/Finite.lean",
      "git_blob": "0c4e8a78345ebbac0f69d012ad8d76d494c14014",
      "sha256": "620c7f7f906e18a27486499cebee59f8c203bc0eb9f21b2deac7681b0ff9427a",
      "bytes": 12234,
      "lines": 246,
      "imports": [
        "AlgebraicAutomata.GreensRelations.Green",
        "AlgebraicAutomata.ForMathlib.Algebra.Group.Opposite"
      ]
    },
    {
      "path": "AlgebraicAutomata/ForMathlib/Algebra/Group/Opposite.lean",
      "git_blob": "c8b27562d0017083c5c58950c165f843062a6ef7",
      "sha256": "f57f98c22804b9088c91e47ad150a2f5d3eff86add3c407cc2940283e44f09c2",
      "bytes": 559,
      "lines": 27,
      "imports": [
        "Mathlib.Algebra.Group.Opposite",
        "Mathlib.Basic.Finite.Defs"
      ]
    },
    {
      "path": "AlgebraicAutomata/GreensRelations/Green.lean",
      "git_blob": "7b68773a5b0eb955e639c8dd657ee5c0921a8ea4",
      "sha256": "3c6666ff900ed5127634b7704d2b4e1a8af3d19d8de82cf4da35d5e03d79e137",
      "bytes": 6863,
      "lines": 156,
      "imports": [
        "AlgebraicAutomata.GreensRelations.MulSeq",
        "Mathlib.Data.Fintype.Card",
        "Mathlib.SetTheory.Cardinal.Finite"
      ]
    },
    {
      "path": "AlgebraicAutomata/GreensRelations/MulSeq.lean",
      "git_blob": "175426cd3d29456750d7d839b222b70f0c58a508",
      "sha256": "051be8987d4861f3ff430342a78798b0231a5cfcd362dd0b5851ceb0bfb829d9",
      "bytes": 8245,
      "lines": 191,
      "imports": [
        "AlgebraicAutomata.GreensRelations.Basic",
        "Mathlib.Basic.Finite.Defs",
        "AlgebraicAutomata.ForMathlib.Algebra.Group.Opposite",
        "Mathlib.Data.Fintype.Pigeonhole"
      ]
    },
    {
      "path": "AlgebraicAutomata/GreensRelations/Basic.lean",
      "git_blob": "1d0114cafdda8ff368c9c99672c5166d3416cdf0",
      "sha256": "1faaf167f7b3c61d765aa77c6c28dcb61093109e5a1b3ab0a34a30597e1c32f6",
      "bytes": 20098,
      "lines": 511,
      "imports": [
        "Mathlib.Algebra.Divisibility.Basic",
        "Mathlib.Algebra.Group.Basic",
        "Mathlib.Algebra.Group.Idempotent",
        "Mathlib.Algebra.Group.Opposite",
        "Mathlib.Algebra.Group.WithOne.Defs",
        "Mathlib.Data.Set.Basic",
        "Mathlib.Logic.Equiv.Basic"
      ]
    },
    {
      "path": "AlgebraicAutomata/FactorizationForest/Regular.lean",
      "git_blob": "e5e2d307cd344563bf0742a02094b265455e3fb9",
      "sha256": "07afc09f4809b3a3624626504b96110f2179699df79fd05ec455c879136e03d3",
      "bytes": 28378,
      "lines": 525,
      "imports": [
        "AlgebraicAutomata.FactorizationForest.Combine"
      ]
    }
  ],
  "direct_external_imports": [
    "Mathlib.Algebra.Divisibility.Basic",
    "Mathlib.Algebra.Group.Basic",
    "Mathlib.Algebra.Group.Idempotent",
    "Mathlib.Algebra.Group.Opposite",
    "Mathlib.Algebra.Group.Subsemigroup.Basic",
    "Mathlib.Algebra.Group.WithOne.Defs",
    "Mathlib.Basic.Finite.Defs",
    "Mathlib.Data.Finset.Max",
    "Mathlib.Data.Fintype.Basic",
    "Mathlib.Data.Fintype.Card",
    "Mathlib.Data.Fintype.EquivFin",
    "Mathlib.Data.Fintype.Pigeonhole",
    "Mathlib.Data.List.Basic",
    "Mathlib.Data.Set.Basic",
    "Mathlib.Logic.Equiv.Basic",
    "Mathlib.SetTheory.Cardinal.Finite"
  ]
}
```

## License and notice inspection

All 14 included upstream Lean files have the same complete original header:

```text
/-
Copyright (c) 2026 Re'em Melamed-Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Re'em Melamed-Katz
-/
```

The tracked distribution contains only one license/notice-named file: root `LICENSE`. Its full 10,763-byte contents are Apache License 2.0, followed by `Copyright 2026 Re'em Melamed-Katz` and the standard application notice. There is no root/nested `NOTICE`, `COPYING` or separate per-file license. The complete closure was checked for embedded copyright/license/author/third-party attribution notices; no conflicting or additional included-source notice was found. The module documentation attributes the mathematical split proof to Thomas Colcombet; these reference comments must also be retained.

No third-party source is bundled in the narrow provider source closure: external Mathlib imports remain dependencies. This inventory does not claim a license audit of all external dependency sources or any newly bundled binary distribution.

Before publication of a port: copy the complete LICENSE beside the vendor tree; preserve every original header; put a prominent dated CCO compatibility-modification notice in every actually changed file; record original hashes and ported hashes separately. A binary/cache redistribution must carry the same applicable full license and notices. A compatibility patch/report supplements those per-file notices. The imported proof remains authored by Re'em Melamed-Katz.

| Upstream metadata | Git blob SHA-1 | SHA-256 |
|---|---|---|
| `LICENSE` | `b38682e47cb82a3693392fb4583a22ea0974e34e` | `765f364be5808dea0db7c84eb1ef084b994b29fb731cd4ea667f8b6aef759b2d` |
| `lakefile.toml` | `a72118b863a5dcc64dfa1c2fa55e80aa0ac0728b` | `2be30054e7e1010ede21fa8ccf5c1245040d62dc4cda46cfe1b9c9a01b26cd9d` |
| `lake-manifest.json` | `9c6da8e64afc271ae0024d897611b7f96b3d525a` | `4cacf5ca8b61dfa9a8175ce87d2998251a0f51132a7fa0ad069a47b394ddb430` |
| `lean-toolchain` | `f0e00b3338bac0d6f050d9a64e277314a9f7830f` | `bc84812c94489d1e3e191baa1dc10d5eb684382d7fe9d2a5ab085e72c1c67e47` |

## Exact upstream environment and transitive manifest

Original toolchain: `leanprover/lean4:v4.35.0-rc3`. Original Mathlib: `2a885768dae569d938bb9ff3474da6a8753bb90a`. The entire upstream Lake manifest contains the following nine Git packages, not just Mathlib:

| Package | Exact revision | Inherited |
|---|---|---|
| `mathlib` | `2a885768dae569d938bb9ff3474da6a8753bb90a` | `False` |
| `plausible` | `b7fb2b866d25bd937a2069931f9733197521cb27` | `True` |
| `LeanSearchClient` | `c35806f43135ab3f254429d0c00bd13fc0123f77` | `True` |
| `importGraph` | `103cd9a46972ee39d9defb2f54ae49823b1228eb` | `True` |
| `proofwidgets` | `87dfe779d5dfd03142ee4fe158911b8eb553ec98` | `True` |
| `aesop` | `a92ed98e694702934d40d12f24a1a449144db43e` | `True` |
| `Qq` | `37b0ba0b26109cf9f9c541f0f9557e50cfa1a3b9` | `True` |
| `batteries` | `950339ce0fd0cc0673a22d87036075737586aed2` | `True` |
| `Cli` | `843844fa601dd56767b1eb22b7ada5b64d5e567a` | `True` |

The complete original manifest, including URLs, scopes, input revisions and configuration paths, is:

```json
{
  "version": "1.3.0",
  "packagesDir": ".lake/packages",
  "packages": [
    {
      "url": "https://github.com/leanprover-community/mathlib4",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "2a885768dae569d938bb9ff3474da6a8753bb90a",
      "name": "mathlib",
      "manifestFile": "lake-manifest.json",
      "inputRev": "2a885768dae569d938bb9ff3474da6a8753bb90a",
      "inherited": false,
      "configFile": "lakefile.lean"
    },
    {
      "url": "https://github.com/leanprover-community/plausible",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "b7fb2b866d25bd937a2069931f9733197521cb27",
      "name": "plausible",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/LeanSearchClient",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "c35806f43135ab3f254429d0c00bd13fc0123f77",
      "name": "LeanSearchClient",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/import-graph",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "103cd9a46972ee39d9defb2f54ae49823b1228eb",
      "name": "importGraph",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/ProofWidgets4",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "87dfe779d5dfd03142ee4fe158911b8eb553ec98",
      "name": "proofwidgets",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.lean"
    },
    {
      "url": "https://github.com/leanprover-community/aesop",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "a92ed98e694702934d40d12f24a1a449144db43e",
      "name": "aesop",
      "manifestFile": "lake-manifest.json",
      "inputRev": "master",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/quote4",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "37b0ba0b26109cf9f9c541f0f9557e50cfa1a3b9",
      "name": "Qq",
      "manifestFile": "lake-manifest.json",
      "inputRev": "master",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover-community/batteries",
      "type": "git",
      "subDir": null,
      "scope": "leanprover-community",
      "rev": "950339ce0fd0cc0673a22d87036075737586aed2",
      "name": "batteries",
      "manifestFile": "lake-manifest.json",
      "inputRev": "main",
      "inherited": true,
      "configFile": "lakefile.toml"
    },
    {
      "url": "https://github.com/leanprover/lean4-cli",
      "type": "git",
      "subDir": null,
      "scope": "leanprover",
      "rev": "843844fa601dd56767b1eb22b7ada5b64d5e567a",
      "name": "Cli",
      "manifestFile": "lake-manifest.json",
      "inputRev": "v4.35.0-rc3",
      "inherited": true,
      "configFile": "lakefile.toml"
    }
  ],
  "name": "AlgebraicAutomata",
  "lakeDir": ".lake",
  "fixedToolchain": false
}
```

Original root Lake options: `pp.unicode.fun=true`, `autoImplicit=false`, `relaxedAutoImplicit=false`, `weak.linter.mathlibStandardSet=true`, `maxSynthPendingDepth=3`; default root `AlgebraicAutomata`. These are provenance, not authorization to migrate CCO. Receiving CCO remains Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; no upstream `.olean` is compatible with that receiving toolchain.

## Actual declaration and E01 correspondence

The global declaration in original Tree.lean is:

```lean
theorem factorization_forest_classical_bound {A S : Type*} [Semigroup S] [Fintype S]
    [Nonempty S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧
      t.IsRamsey eval ∧
      t.height ≤ 3 * Fintype.card S - 1
```

`FactorizationTree A` has leaf `a`, binary `(l,r)`, and idempotent node with an **ordered List** of children. `value` is literal list yield: singleton at a leaf, append at binary node, recursively concatenated child yields at idempotent node. Height is zero at a leaf and one plus maximum child height at internal nodes. `IsRamsey eval` recursively validates children; an idempotent node must have at least two children and one common evaluation `e` satisfying `IsIdempotentElem e`. Hence every node of arity at least three has the exact common-idempotent property required by E01. Syntactically malformed empty/unary idempotent nodes exist as terms of the raw inductive type, but cannot satisfy `IsRamsey`; claims about absence of unary/empty nodes must be restricted to a valid Ramsey tree.

No unit, monoid, commutativity, or empty-word multiplication law occurs. The total `eval` needs some value at `[]`, but the append law is requested only for two nonempty lists. In CCO's zero-completed semigroup the zero supplies both nonemptiness and an arbitrary empty-list evaluation. The stronger natural-number bound `3*card S-1` implies E01's `3*card S` without changing obstruction constants. The theorem preserves the exact original word, not merely its evaluated image.

The required later CCO adapter is still substantive: instantiate the actual typed positive zero-completed semigroup, prove its semigroup/evaluation laws, and preserve the child intervals, macro-letter occurrences and original root yield in the CCO encoding; rule out zero on each actual subtree interval. This inventory supplies no such B058 adapter or obstruction theorem. Kufleitner2008 remains E01's published citation; the imported implementation follows Colcombet's split route and need only imply the same statement.

## Evidence limits and receiving compatibility seam

This agent performed no build and issued no transitive axiom audit. Source token scan on the 14-file closure finds no `sorry`, `admit`, declared `axiom`, `unsafe`, `implemented_by` or `sorryAx`. That scan is not compiled soundness evidence.

The direct imports `Mathlib.Basic.Finite.Defs` in `ForMathlib/Algebra/Group/Opposite.lean` and `GreensRelations/MulSeq.lean` are an expected newer-Mathlib path compatibility seam. Their receiving replacement must be justified by actual API use and verified by compilation, without broad Mathlib imports or mathematical strengthening. Module/public syntax and tactics may expose further routine compatibility edits. The separate port/build agent owns those determinations and modifications.
