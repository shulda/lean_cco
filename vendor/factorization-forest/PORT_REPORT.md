# Factorization forest provider — receiving compatibility preparation

Date: 6 November 2026. Actual compatibility author: `/root/b053_resume`.
Actual read-only upstream inventory: `/root/b053_resume/forest_inventory`.
The imported formalization and original proof are by Re'em Melamed-Katz.

## Scope and current result

The exact finite Tree import closure has been ported and replayed successfully
on the existing receiving Lean 4.34.1 / Mathlib v4.34.1 environment. All
fourteen source modules and a small arbitrary-semigroup consumer compile.
The receiving protocol's complete transitive axiom audit checks **791
provider declarations**, with only `propext`, `Classical.choice`,
`Quot.sound`, **zero violations** and no `sorryAx`.

This is explicitly authorized advance provider preparation under
`formalization/FACTORIZATION_FOREST_PROVIDER.md`, based on main
`68faa81d1d2af95ad58f6937afdd1afd97bb49ad`. It is **not a B058 claim or
completion**, an accepted dependency, an independent implementation review,
or the concrete adapter for CCO's typed zero-completed semigroup. No parent
CCO source, root imports, Lake configuration/manifest, toolchain, policy,
provider pin or coordination STATE has been changed.

## Immutable source, closure and environment

- Upstream: `https://github.com/ReemMelamed/algebraic-automata`, exact commit
  `0acb244aaa913c32eeeff48e939cb5df469a3f70`.
- Narrow root: `AlgebraicAutomata.FactorizationForest.Tree`; **14 original
  Lean files / 4,079 original lines / 184,508 original UTF-8 bytes**.
- Upstream Lean: `leanprover/lean4:v4.35.0-rc3`; upstream Mathlib:
  `2a885768dae569d938bb9ff3474da6a8753bb90a`.
- Receiving Lean: `leanprover/lean4:v4.34.1`, compiler commit
  `5045d0056413266e57c625dcd7c365b10e377c52`, Linux/x86_64.
- Receiving Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
  The complete receiving nine-package transitive manifest is at this
  package root; the complete original nine-package upstream manifest and
  configuration are preserved verbatim under `upstream/`.
- `PROVENANCE.json` records every included original Git blob/SHA256 and
  every ported source SHA256. These original fingerprints were checked
  directly against the clean exact detached upstream checkout.
- `INVENTORY.md` preserves the separate actual reader's exact source,
  import, license and signature inventory. All sixteen direct external
  imports are specific Mathlib modules. The infinitary, TreeToSplit,
  application and original umbrella modules are excluded.

No Lean 4.35 `.olean` was copied or loaded. All fourteen receiving provider
modules were compiled from their current source. The exact already built
receiving dependency packages were read only, with each of their nine Git
pins verified before replay. Every provider output was written into this
package's own `.lake/build`; no shared build directory was modified.

The upstream Lean 4.35 environment was **not locally replayed** in this
preparation. Its pinned successful upstream CI remains historical source
evidence, not a newly performed local build. The new actual evidence here
is the receiving Lean 4.34 source/consumer replay and transitive audit.

## Precisely bounded compatibility edits

Every imported source retains its original header and adds a prominent
CCO compatibility-port modification notice. One original trailing blank
line in `ForMathlib/Algebra/Group/Opposite.lean` is normalized for the
receiving whitespace check. Beyond these nonsemantic edits, only two
source files change, and only their existing proof terms change:

| File | Receiving compatibility change |
|---|---|
| `GreensRelations/Basic.lean` | Replace unavailable opposite-divisibility names with explicit transported multiplication witnesses / receiving `rightDvd_iff_op_dvd_op`; replace `WithOne.cases_on` with `WithOne.recOneCoe` to retain the `one`/`coe` branch API. |
| `FactorizationForest/Tree.lean` | Replace five unsupported `lia [facts]` forms with explicit local facts or `simp only` followed by `omega`. |

All original declaration names, theorem statements, hypotheses, tree types,
height/yield/IsRamsey definitions and mathematical bounds are unchanged.
`compatibility.patch` contains the complete source delta relative to the
pinned upstream closure, including all per-file notices (zero-context
unified patch; apply with `git apply --unidiff-zero`). There are no broad
Mathlib imports, admissions, added mathematical axioms or unsafe proof
substitutions. The exact closure token scan found none of `sorry`, `admit`,
`axiom`, `sorryAx`, `unsafe`, `implemented_by` in the included Lean sources.
The expected `Mathlib.Basic.Finite.Defs` path was available in the receiving
Mathlib and needed no compatibility change.

## Actual API and consumer

`Tests/Consumer.lean` imports only the narrow Tree root and applies the
unchanged global `factorization_forest_classical_bound` under exactly
`[Semigroup S] [Fintype S] [Nonempty S]`, arbitrary alphabet `A`, a total
`eval : List A → S`, multiplicativity on concatenations of two **nonempty**
words, and a nonempty input word `u`. The result is a literal tree `t` with
`t.value = u`, `t.IsRamsey eval`, and
`t.height ≤ 3 * Fintype.card S - 1`.

The consumer also reads back the actual signature, theorem axioms,
`FactorizationTree.tree_value_ne_nil` and the idempotent-node equivalence.
Leaf height is zero, child order/yields are literal lists, a valid
idempotent node has at least two recursively valid children, and all its
children have one common idempotent evaluation. No multiplicative identity
or empty-word multiplicativity is introduced. This supports the future
receiving work order; it does not construct its typed semigroup, prove
its nonempty append law, or perform its tree conversion.

## Replay and audit evidence

`tools/build_readonly.py` reads the exact package compiler options from
`lakefile.toml` and passes all of them to every compiler invocation:

- `pp.unicode.fun=true`
- `autoImplicit=false`
- `relaxedAutoImplicit=false`
- `weak.linter.mathlibStandardSet=true`
- `maxSynthPendingDepth=3`

The final complete replay is successful: fourteen provider source modules,
`Tests.Consumer`, and the full module-origin-based transitive axiom audit
of **all 791 AlgebraicAutomata declarations imported by Tree**, not merely
the final theorem or a namespace-name guess. The audit imports the exact
Tree root under the unchanged three-axiom allowlist.

Durable text evidence:

- `evidence/receiving-replay.log`: complete successful replay, elaborated
  consumer signatures, target axiom readback and audit summary.
- `evidence/receiving-axiom-audit.json`: 791 declarations / zero violations.
- `evidence/replay-receipt.json`: exact source hashes, dependency manifest,
  compiler and options for the successful run.
- `evidence/environment.json`: OS/architecture, configuration fingerprints,
  read-only dependency location and output/redistribution scope.

Earlier feasibility failures were ordinary receiving API differences listed
above. An initial audit wrapper invocation lacked the compiler in PATH;
that wrapper was corrected and the full final replay/audit above succeeds.
No failed feasibility run is presented as a proof result.

## Licensing and attribution completion

The full original Apache-2.0 text is retained at `LICENSE`, with its original
copyright. Every one of the fourteen included Lean sources retains the
original Re'em Melamed-Katz copyright/license/author header, including its
original wording; every copied/ported source additionally names the CCO
compatibility modification and purpose. Original `README.md` is preserved
as `UPSTREAM_README.md`. No `NOTICE`, `COPYING`, separate file license, or
bundled third-party source was found anywhere in the exact chosen upstream
distribution. Root Apache licensing is consistent with all included headers.

No compiled artifacts are committed or distributed by this preparation.
Any later separate source/cache/binary distribution must retain `LICENSE`,
applicable original/compatibility notices and exact provenance. Compilation
is not an exception to that requirement. Original mathematical references
remain separate: the article cites Kufleitner 2008, Theorem 1; this Lean
formalization follows Colcombet's split construction. No authorship of the
imported formalization is attributed to the CCO team.

## Remaining receiving duties

No mathematical provider gap or source-contract change was needed for this
compatibility port. Before it becomes an accepted dependency, the actual
non-author must review the pinned closure, exact compatibility delta,
licensing/provenance, consumer and successful exact-head CI/audit under the
ordinary protocol. Root is the sole publisher; no PR/push/CAS or approval
was performed by this author. Provider output caches have not been packaged.

B058 remains separate. Its future adapter must construct the actual finite
S_typ including incompatible-product zero, prove associativity and the
nonempty-word append law, convert the actual ordered tree while preserving
every macro occurrence and contiguous nonempty interval, exclude zero on
those intervals, and feed the original bounded-obstruction export without
changing constants or leaving a forest-provider premise. None is claimed
by this isolated provider preparation.
