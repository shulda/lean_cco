# Independent source review — advance factorization forest provider preparation

Date: 6 November 2026. Actual reviewer identity: `/root/b053_fresh_review`;
registered actor: `work_control_20261106d`.

**Source review result: no findings in the exact frozen preparation below.**
This is a review of advance provider preparation, not formal approval to
integrate a provider, a package review lease, an accepted dependency, or a
B058 claim/completion. The earlier B053 review lease has ended. No provider
CI/cache/facade/CCO adapter is approved by this report.

## Exact reviewed snapshot and independent provenance

| Item | Exact identity |
|---|---|
| Native candidate commit | `0e60b7c27bec925ea87b53daae58bc49024b1ed3` |
| Native candidate tree | `f8617d1d139f34cb575207e8218446580244aa0a` |
| Public draft PR | `https://github.com/shulda/lean_cco/pull/78` |
| Public preparation head | `176e72f7174b37a1dbbd1c0761e655b950f08f3c` |
| Public preparation tree | `f8617d1d139f34cb575207e8218446580244aa0a` |
| Candidate parent/base | `68faa81d1d2af95ad58f6937afdd1afd97bb49ad` |
| Original upstream source | `ReemMelamed/algebraic-automata@0acb244aaa913c32eeeff48e939cb5df469a3f70` |
| Narrow provider root | `AlgebraicAutomata.FactorizationForest.Tree` |

I personally fetched the exact public Git commit and PR metadata: the PR
is draft and its public commit has the identical full tree above. I also
verified the native worktree was clean at the stated commit. Its change
from its parent is exactly 35 added files: the isolated
`vendor/factorization-forest/` directory and the preparation report at
`formalization/coordination/reports/work-factorization-forest-provider-prep-20261106.md`.
Parent CCO sources, root imports, package configuration/manifest/toolchain,
existing provider pins, policy and coordination STATE are unchanged.
`git diff --check HEAD^ HEAD` passes.

I did not author the upstream formalization, compatibility changes,
provider interface, helper, inventory or candidate reports, and did not
participate in their implementation, design or repairs. The compatibility
author is `/root/b053_resume`; the separate upstream inventory reader is
that author's child `/root/b053_resume/forest_inventory`. Their reports
oriented this review but are not borrowed independent approval. I read the
sources and evidence myself and changed no candidate file. Root remains
the sole publisher.

## Complete personal reading and original-source comparison

I read the full `formalization/FACTORIZATION_FOREST_PROVIDER.md` work order,
including its licensing and advance-preparation limits. I read every line
of all fourteen current closure sources:

- `FactorizationForest/{Basic,Combine,Irregular,Regular,Split,Tree}.lean`;
- `GreensRelations/{Basic,Finite,Green,MulSeq,Order}.lean`;
- `ForMathlib/Algebra/Group/Opposite.lean`;
- `ForMathlib/Data/List/{SemigroupProd,Slice}.lean`.

These paths are relative to the candidate's `AlgebraicAutomata/` directory.
I also read the complete compatibility patch, provenance JSON, original
full license, upstream README, upstream and receiving configurations and
complete manifests, inventory, port/preparation reports, standalone README,
consumer, build helper, replay receipt, environment record and complete
successful replay/audit log. I checked the E01/A09 and C04–C06 receiving
contract and the original `typed-factor-path`/nonzero-interval application.
This report does not review the whole future B058 implementation.

I personally obtained the complete upstream recursive Git tree at the
exact pin, then checked the clean exact local upstream checkout and every
included file against its pinned Git blob and SHA256. All fourteen
original blob IDs, SHA256 values and byte counts in `PROVENANCE.json`
match. Original closure size is 14 files, 4,079 lines and 184,508 UTF-8
bytes. The frozen port is 4,191 lines and 189,122 bytes. Every current
source SHA256 agrees with both provenance and the successful replay
receipt. The original LICENSE/README/configuration/manifest/toolchain
copies match their original upstream bytes exactly.

I independently followed ordinary and `public import` edges from Tree.
The closure is exactly the fourteen inventoried files, with sixteen
specific external Mathlib imports. It excludes the original umbrella,
applications, `Infinitary.lean` and `TreeToSplit.lean`. There is no broad
`Mathlib` or `Mathlib.Tactic` import. My closure token scan finds none of
`sorry`, `admit`, `axiom`, `sorryAx`, `unsafe` or `implemented_by`.

I regenerated the complete zero-context unified source diff in memory;
it equals `compatibility.patch` byte for byte. Apart from the prominent
notice in every copied source and one original trailing blank-line
normalization, only existing proof terms change:

- `GreensRelations.Basic` transports actual opposite multiplication
  witnesses to replace an unavailable divisibility lemma, uses the
  receiving equivalent opposite-divisibility lemma, and changes the
  `WithOne` recursor with the same one/coercion branches.
- `FactorizationForest.Tree` replaces five unsupported `lia [facts]`
  invocations with explicit local facts or `simp only` and `omega`.

I read both sides of those changes. They preserve declaration names,
statements, assumptions, definitions and mathematical bounds. There is
no added provider premise or strengthening of the theorem's hypotheses.

## Mathematical API and proof dependency review

The actual global theorem has arbitrary alphabet `A`, arbitrary
`[Semigroup S] [Fintype S] [Nonempty S]`, total `eval : List A → S`, and
the law

```lean
∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v
```

For each nonempty original word `u`, it constructs an actual
`FactorizationTree A` satisfying literal `t.value = u`, `t.IsRamsey eval`
and `t.height ≤ 3 * Fintype.card S - 1`. There is no monoid, unit,
commutativity, finite-alphabet or empty-word multiplicativity assumption.
The standalone consumer applies exactly this signature.

I traced the finite Green-relation and regular/irregular D-class arguments,
the decreasing `nSElement` split construction and `nS ≤ card S` bound,
the ordered sequence/interval combination, and the conversion from the
normalized word split to the tree. The conversion uses the original
ordered word slices and literal concatenated yields; it does not replace
the word by another word with the same evaluated image. The final height
bound uses the normalized split and then the cardinal bound.

Leaves have height zero. Binary nodes preserve the ordered two yields.
Idempotent nodes have an ordered list of children; `IsRamsey` requires
at least two recursively valid children and a single common idempotent
evaluation for all of them. The raw inductive type permits malformed
empty/unary idempotent terms, but the proved Ramsey condition excludes
them. `tree_value_ne_nil` proves every valid subtree yield is nonempty.
Thus the provider supplies the finite-semigroup ordered forest needed by
E01, with a stronger bound than the receiving `3 * card S` convention.
It does not by itself prove that a subtree has nonzero value in the
future typed zero completion: that is the separate actual C06 duty.

## Receiving replay and personally checked audit

The receiving package remains Lean `4.34.1`, compiler commit
`5045d0056413266e57c625dcd7c365b10e377c52`, Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, and the complete current
nine-package manifest. I personally checked the compiler version and all
nine dependency Git revisions, and all recorded configuration, helper,
consumer and audit source/executable fingerprints.

I read the entire final author replay log: all fourteen provider sources
and `Tests.Consumer` compile successfully with the five exact package
options recorded in the receipt. The log reads back the unchanged
theorem and tree signatures. The helper builds all local provider sources
in dependency order into its private output directory; shared dependency
builds are only inputs. The checked final source hashes match this exact
commit. No upstream Lean 4.35 artifact is part of the preparation.

I personally read the receiving audit's `Main.lean` and `AxiomAudit.lean`.
Its candidate selection uses defining-module origin under
`AlgebraicAutomata`, so global declarations such as the final theorem
are included despite having no `AlgebraicAutomata` namespace prefix.
It traverses declaration types and values transitively and fails on an
empty audit or disallowed axiom.

I then independently reran that executable read only, importing the
current Tree output with the exact receiving dependency search path:

```json
{"allowed":["propext","Classical.choice","Quot.sound"],"audited":791,"axiomsUsed":["propext","Classical.choice","Quot.sound"],"ok":true,"root":"AlgebraicAutomata","violations":[]}
```

This exactly matches the committed audit JSON. I did not rerun the full
source compilation or perform a new upstream Lean 4.35 build. The new
receiving source compilation evidence is the personally read, hash-bound
author replay; the second compiled-environment audit above is my own run.
Neither is an exact-head GitHub provider CI/integration approval.

Evidence SHA256 values independently verified:

| File | SHA256 |
|---|---|
| `PROVENANCE.json` | `a3de66400ebc17a3be0f3f36f093ebcf747954de0485113e17fd24aa04f25578` |
| `compatibility.patch` | `017d1c2802a4bac2728a32d757e7f9db14794816e0d92d6e290f700f57e711a5` |
| `evidence/receiving-replay.log` | `0d045dfbe180bc5e88a0b4c7c32e526d2623b8887ab5129ea6188487ebcf365f` |
| `evidence/replay-receipt.json` | `4bd127f5d2636aa899a6dec0eef0c263e67de8f1340ec2e9e000dd1142372ac6` |
| `evidence/receiving-axiom-audit.json` | `dd7c1d4c2acf0ac9bce7488373aa765eea8d71aa243a5b043fb39647f2f7f117` |

## License and attribution review

The full original Apache-2.0 LICENSE is retained next to the imported
source. Every included file preserves the original Re'em Melamed-Katz
copyright/license/author header and has a prominent dated CCO compatibility
modification notice. The complete exact upstream distribution has thirty
tracked files, root LICENSE as its only license-named file, and no
root/nested NOTICE or COPYING path. Source reading found no conflicting
or additional included-source attribution. The original mathematical
references are retained; imported formalization authorship is correctly
attributed to Re'em Melamed-Katz, while compatibility authorship is
separate. The upstream README is preserved verbatim.

No compiled artifact is committed in this candidate. The reports correctly
state that any later standalone cache/binary distribution must retain the
full license, applicable original/modification notices and provenance.
This is a review of the included distribution, not a separate license
audit of every external dependency.

## Explicit remaining duties

The preparation is useful and source-consistent at the exact frozen
head, but these receiving obligations remain open:

1. Ordinary authorized publication/integration with the applicable fresh
   exact-head review, successful provider-aware CI/build/audit and a
   successful resulting-main check. The current unchanged CCO workflow
   does not compile or audit this unimported standalone provider.
2. Receiving package/facade/root-closure plumbing and verification of all
   affected consumers. The isolated root is not yet a CCO dependency.
3. If provider outputs are cached or redistributed, complete source,
   toolchain/manifest/compiler-option and output identity verification,
   reproducible validation, and applicable license/notice packaging.
   The local replay receipt is not an accepted cache protocol.
4. The separate B058 C04/C05/C06 adapter: construct the actual finite
   associative typed zero-completed semigroup, prove its nonempty append
   law, instantiate this exact theorem, preserve every original macro
   occurrence and ordered contiguous nonempty subtree interval, and prove
   the actual interval values nonzero. Then the supplied height bound can
   discharge the original source forest application without altering
   constants or leaving a forest-provider premise.

No source-contract change or mathematical gap was found in this bounded
compatibility preparation. The six existing external receiving records
and the unbound E01/B058 status remain unchanged. This report records
source/provenance/license/replay review only; no acceptance or integration
approval is issued.
