# Factorization forest: pinned Lean provider and receiving work order

Recorded 29 October 2026. This is preparation for the receiving Lean team,
not a package allocation, dependency installation or compiled CCO adapter.
The mathematical provider remains `old_idempotent_forest/E01`; there are
still SIX external records, not a seventh theorem.

## Existing implementation

| Item | Pinned reference |
|---|---|
| Repository / author | [ReemMelamed/algebraic-automata](https://github.com/ReemMelamed/algebraic-automata), Re'em Melamed-Katz |
| Commit | `0acb244aaa913c32eeeff48e939cb5df469a3f70` |
| Narrow import | `AlgebraicAutomata.FactorizationForest.Tree` |
| Declaration | `factorization_forest_classical_bound` (global namespace) |
| Source | [Tree.lean, lines 642 onward](https://github.com/ReemMelamed/algebraic-automata/blob/0acb244aaa913c32eeeff48e939cb5df469a3f70/AlgebraicAutomata/FactorizationForest/Tree.lean#L642) |
| Lean | `leanprover/lean4:v4.35.0-rc3` |
| Mathlib | `2a885768dae569d938bb9ff3474da6a8753bb90a` |
| License | Apache-2.0; preserve attribution when copying/porting |
| Exact-pin upstream build | [successful CI 40362358302](https://github.com/ReemMelamed/algebraic-automata/actions/runs/40362358302) |

The actual signature assumes `[Semigroup S] [Fintype S] [Nonempty S]`,
an arbitrary alphabet A, an evaluation `eval : List A -> S` multiplicative
on concatenations of two NONEMPTY lists, and a nonempty word u. It returns
a `FactorizationTree A` with `t.value = u`, `t.IsRamsey eval` and
`t.height <= 3 * Fintype.card S - 1`. A value on the empty list is required
by the total Lean function type but no empty-word multiplicativity is assumed.
In our zero-completed semigroup it can be chosen to be zero, not a unit.

The checked definitions give leaf height zero, binary concatenation, and
ordered list-valued idempotent nodes. `IsRamsey` requires each idempotent
node to have at least TWO children, recursively valid trees and one common
idempotent evaluation for every child. Thus every node with at least three
children has precisely our required property. There are no unary nodes or
empty leaves in a valid tree. Binary idempotent nodes cause no mismatch.

All 20 repository Lean files were scanned at this pin (6,795 lines): no
`sorry`, `admit`, declared `axiom`, `unsafe`, `implemented_by` or `sorryAx`
token was found. Source inspection plus successful upstream CI is the
current evidence. No independent local build, transitive compiled-axiom
audit or receiving-toolchain port has yet been performed. The theorem's
import closure uses the finite split construction; the separate infinitary
compactness development need not be imported.

## Licensing and attribution — required receiving steps

Added 30 October 2026 at the author's request. This is a concrete integration
requirement, separate from the mathematical/API/build acceptance gates.

The pinned upstream `LICENSE` is Apache License 2.0 and names
`Copyright 2026 Re'em Melamed-Katz`. The actual
`AlgebraicAutomata/FactorizationForest/Tree.lean` header explicitly says
that it is released under Apache 2.0 and identifies the same author.
Retain that header, including the copyright notice. The words “All rights
reserved” there do not cancel the accompanying express license grant.

Before publishing the receiving port or distributing its compiled outputs:

1. **Inventory the exact imported source closure.** Record the upstream
   repository, full commit, paths and original blob hashes; inspect each
   included file and any bundled third-party material for its own license
   and notices. Preserve applicable upstream author/copyright notices.
   A root license must not silently overwrite a separately licensed file.
2. **Include the full Apache-2.0 license text.** If vendoring, retain it
   beside the copied provider, e.g. `vendor/factorization-forest/LICENSE`.
   If using a pinned external Lake package, retain its original license
   and ensure any separately redistributed source or binary archive also
   supplies a copy. Do not replace the full text with only a URL.
3. **Mark modifications in the modified files.** Every ported source file
   must carry a prominent notice identifying that it was changed for the
   CCO compatibility port (and preferably its date/purpose). Retain the
   original notices; a separate compatibility patch and provenance report
   supplement, rather than replace, these per-file modification notices.
4. **Preserve any upstream NOTICE content if present.** No root `NOTICE`
   was found at the recorded pin; check the actual chosen distribution
   and included material again at integration time. If present, reproduce
   its applicable attribution notices as required by Apache-2.0 section 4.
5. **Keep ownership explicit.** Attribute the imported formalization to
   Re'em Melamed-Katz, distinguish our compatibility edits and CCO adapter,
   and record the original mathematical references separately. Do not
   describe the imported proof as newly authored by the CCO team.
6. **Cover compiled redistribution too.** Cached `.olean`/native artifacts
   remain build products of the licensed provider. Any published standalone
   provider cache, release archive or other redistributed binary bundle
   must carry the required license/notices with its provenance. Compilation
   or caching does not remove these obligations.
7. **Record completion in the integration report/review.** List the retained
   license/notice paths, exact source pin, inspected closure and modification
   notices before approving the provider integration. Keep our own adapter
   licensing distinct; Apache-2.0 does not require relicensing the whole CCO
   project. Ordinary licensed use needs no separate individual permission;
   investigate a concrete license conflict if the inventory finds one.

Authoritative references:
- [Pinned upstream LICENSE](https://github.com/ReemMelamed/algebraic-automata/blob/0acb244aaa913c32eeeff48e939cb5df469a3f70/LICENSE).
- [Pinned Tree.lean header](https://github.com/ReemMelamed/algebraic-automata/blob/0acb244aaa913c32eeeff48e939cb5df469a3f70/AlgebraicAutomata/FactorizationForest/Tree.lean).
- [Apache License 2.0, especially sections 2 and 4](https://www.apache.org/licenses/LICENSE-2.0).

## When it is needed

The first actual application is **B058**, `old_idempotent_forest/C05`,
in `sections/v27/16_old_idempotent_forest.tex`, proof of
`lem:typed-factor-path` (line 240 at the frozen source pin). C04 constructs
the finite typed zero-completed semigroup; C06 supplies the nonzero-interval
argument. The resulting obstruction bound C58 feeds B059's concrete hidden
HN application (`terminal_hidden_hn/C32`, then C36).

Do not confuse this with B027 `thm:locality-bound`: its earlier bad-cycle
bound is a finite-state acyclicity argument using B026 saturation and does
NOT use a factorization forest. Generic B037 HN transfer can also be proved
with a supplied obstruction bound before this geometric instantiation.
The inactive legacy source04 contains an older forest invocation; the
preferred article route uses source06--18, not that legacy file.

At the read-only receiving snapshot `shulda/lean_cco/main` commit
`0da0e9f6d47fe956a8d64eb767ce39a211ceea87`, the released catalogue includes
B027 and B032 but not B058. Hence this is sensible advance dependency work,
not a new blocker for the early batches. Re-read live policy and STATE when
scheduling; this observation is not a claim about future active branches.

## Implementation sequence and acceptance evidence

1. **Independent provider preparation can start before B058.** Pin the
   repository commit and full transitive manifest in an isolated build on
   its own toolchain. Build the narrow Tree module and a small consumer
   importing it; inspect the elaborated signature and run the receiving
   protocol's transitive axiom audit, including absence of `sorryAx`.
   Retain the exact-head log and environment pins. An upstream green badge
   or token scan is not this acceptance evidence.
2. **Choose one compatible receiving environment.** The observed CCO main
   uses Lean v4.34.1 and Mathlib v4.34.1; this provider uses v4.35.0-rc3 and
   the Mathlib SHA above. Decide under the normal receiving protocol whether
   to port the finite provider closure to the current environment or migrate
   CCO/HKN/HN together. HN's recorded Lean version matches this provider,
   but that alone does not establish Mathlib/API compatibility. Do not mix
   `.olean` files from different toolchains or silently upgrade shared CI.
3. **Build the CCO adapter once C04's actual semigroup is available.** Use
   the genuine S_typ including the incompatible-product zero and positive
   STRONG profile multiplication. Prove associativity and finiteness,
   evaluate only nonempty original macro words, and prove the required
   append law. No global identity or equality atom is adjoined. Apply the
   pinned declaration and weaken `3*card S_typ-1` to the existing `3*card
   S_typ` bound without changing the obstruction constants.
4. **Convert the actual tree, preserving data.** Prove that child yields
   partition each parent's original word into ordered NONEMPTY contiguous
   intervals. Preserve every original macro-letter occurrence, root yield,
   leaf order and height; nodes have at least two children and wide nodes
   share one idempotent. Do not replace a branch word by another word of
   equal profile. Our C06 proof then excludes zero on every subtree interval
   of the composable original path, giving a same-sort positive idempotent.
5. **Connect existing B058 proofs.** Supply C05/C06 to T03, retain the
   already prepared stopped-pruning argument, and keep structural supplied-
   tree C27 independent of E01. Reinsert maximal deleted gaps over ONE old
   complete base with the fixed original anchor. Demonstrate the precise
   bounded-obstruction export used by B059; no new forest assumption may
   remain hidden in that instantiated theorem.

Cache the audited dependency build as described in
[EXTERNAL_PROVIDER_BUILD_CACHE.md](EXTERNAL_PROVIDER_BUILD_CACHE.md).
Use the exact provider/toolchain/transitive pins, OS/architecture and build
configuration as the dependency key, not each changing CCO commit. Keep
ordinary incremental-build reuse distinct from any required fresh replay.

## Fallback and scope

Reuse this implementation unless the build/axiom/compatibility audit exposes
a concrete reason not to. If a port is more expensive than a fresh proof,
formalize a standalone finite-semigroup forest theorem and then reuse the
same adapter. A weaker uniform height bound may suffice for the mathematical
method, but replacing `3|S_typ|` requires explicitly updating every numerical
bound and article contract; it must not silently satisfy the current E01.

The published theorem citation remains Kufleitner 2008, Theorem 1. This
Lean implementation follows Colcombet's split route; a provider need not
reproduce the cited proof when its actual theorem implies the same contract.
The manuscript bibliography clarification stays in the human follow-up
queue. No HKN assumption is added to the Ramsey branch.
