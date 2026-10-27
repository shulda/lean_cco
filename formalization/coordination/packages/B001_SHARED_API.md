# B001 — shared represented API, SAP geometry and a real consumer

Contract revision 1. Owner: Project 1, after activation in `BOARD.json`.
This is the first **substantial project package**, not a request to prove
one lemma. It covers the elementary parts of both foundational streams and
two small group-action exports. The exact source pin and file hashes are in
the board. No Lean representation in this document has already compiled.

## Outcome and source boundary

Deliver one working Lean/Lake repository whose shared vocabulary is usable
by the later RAW and STRONG projects. Prove enough mathematics to expose
representation mistakes before those projects start. Work internally through
M1–M4; these milestones are not four separately assigned ChatGPT projects.

Required mathematical scope:

| Source | Included part |
|---|---|
| `formalization/raw_exact/PROOF_NOTES.md`, N01–N02; `sections/exact_foundations/01_full_raw_exact_helly.tex` | Actual orbitals, seriality, elementary typed relation algebra, same-sort commutation/equivalence joins, words and equality normalization: RAW C01–C05. |
| `sections/typed_invariant_quotient_transport.tex` | `lem:prescribed-action-point-lifting` and the full `lem:foundational-orbital-pullback`, including the empty-diversity exception. |
| `sections/typed_strong_domains.tex`; `formalization/strong_selectors/PROOF_NOTES.md`, N01–N03 | Actual triangle product, SAP algebra/Set-Pasch, supported-fork duplication, stabilizer orbit infinitude and injectivization: STRONG C01–C05. |
| `sections/stationary_independence_from_HS.tex`, base-path menu definition only | A small independent consumer of the shared finite-set/embedding/product API; no SIR theorem is claimed by this package. |

This is several pages of proof mathematics before Lean-specific conversions.
Do not expand it to full RAW Helly, strong CCO exactness, selectors, parity,
Hasse, EPPA or Ramsey. In particular do not use RAW Helly to shortcut STRONG
geometry. Source claims beyond the listed range belong to later packages.

## M1 — repository and representations

Validate and extend the initial Lean/CI scaffold in the **bound public
repository**, never in the manuscript preparation repository. The coordinator
may already have supplied a tested scaffold; inspect its runbook, exact pins
and real CI result before changing it. If no scaffold exists, create one
with a tested compatible Lean/mathlib pin. Keep committed `lean-toolchain`,
Lake configuration and `lake-manifest.json`. Do not import
the EPPA or Ramsey repositories in B001; their future version compatibility
is a separate integration obligation.

Use a single Linux build initially, appropriate mathlib caching, and checks
on PRs and the default branch. Avoid redundant simultaneous full builds.
Write the actual build and audit commands in the report/runbook, including
how to check that all exported modules are built. The currently documented
official starting points are [Lake](https://lean-lang.org/doc/reference/latest/Build-Tools-and-Distribution/Lake/)
and [lean-action](https://github.com/leanprover/lean-action); review their
current instructions at implementation time rather than copying an untested
workflow from this preparation.

Reuse mathlib relations, actions, quotients, finite sets and embeddings when
their semantics fit. Choose and record one shared representation for:

- a finite type of named sorts and their nonempty real carriers;
- actual complete atomic pair colourings, finite palettes and typed converse;
- logical identity on loop sorts, distinguished from diversity atoms;
- typed supports as represented relations and as sets of atoms, with a proved
  correspondence for invariant supports;
- composable typed words, including a genuine empty loop word;
- finite typed partial diagrams, homomorphisms and injective realizations;
- finite **complete** induced structures, induced embeddings and partial
  isomorphisms; the pointwise stabilizer of a finite real set;
- homogeneous-source, age/SAP and semantic homomorphic CCO interfaces, with
  the hypotheses kept separate.

A family of carriers indexed by sorts is fine; a common carrier with a sort
map is fine. When discussing equality across sorts use the resulting tagged
real universe. Different tags are disjoint; repeated sort labels never make
two distinct formal vertices equal. Do not encode equality of distinct-root
diversity pairs by adjoining a fake identity atom.

An empty restriction list evaluates to the full typed relation/palette. An
empty RAW word evaluates to actual Id. A positive strong word has at least
one diversity letter. A set of atoms keeps its ordered sort-pair tag even
if its underlying encoding happens to match another palette.

The CCO interface is for finite specified **diversity** diagrams: if each
specified simple cycle has a colour-preserving homomorphism into the source,
the whole diagram has one. Missing edges permit collisions. Only cycles of
length at least three count; no parallel edges, invented equality edges or
automatic injectivity are allowed. Define the interface now; prove no CCO
completion theorem in B001. Do not burden elementary algebra with a CCO
premise merely because the source section has a stronger ambient setting.

Record candidate public filenames/namespaces after the first compiled
implementation. Keep public representation conversions in the shared core;
each later stream must be able to import it without importing the other
stream's Helly or exact-calculus theorem.

## M2 — RAW relations, actual orbitals and quotient witnesses

For represented typed relations use

\[
 (R;S)(x,z)\iff\exists y\;(R(x,y)\land S(y,z)).
\]

Prove the usual typed associativity, identity, monotonicity and reversed
converse laws by actual witnesses. Prove concatenation/reversal laws for
words and deletion of logical identity **letters**. Deleting such letters
does not remove identity **outputs** of a nonempty diversity walk.

For a group acting transitively on each inhabited original sort, prove that
any nonempty invariant relation is serial and coserial at every point.
Derive nonemptiness of compatible invariant products and correctly typed
Top absorption. With a complete homogeneous atomic source, prove that atoms
are the actual ordered-pair orbitals and that invariant supports correspond
to unions of them. Establish atomic typed Peirce using pair-orbit uniformity.

Only for endorelations on an original sort whose pair orbitals are symmetric,
derive commutation of invariant relations. For two such invariant
equivalences derive represented composition equals their join. Do not state
mixed-sort commutativity or distributivity of the full equivalence lattice.

Prove the two following source exports for arbitrary group actions with
their own minimal hypotheses; homogeneity, SAP and CCO are not parameters.

**Prescribed-action lifting.** For a nonempty K-set Y, a Gamma-set B, a
homomorphism rho:K→Gamma and an equivariant surjection pi:Y→B,
surjectivity of rho and transitivity of ker(rho) on every fibre are equivalent
to: for every x,y and gamma with gamma·pi(x)=pi(y), there is k with
rho(k)=gamma and k·x=y. Do not assume faithful actions or a group section.

**Actual orbital pullback.** Let G act transitively on inhabited root sorts
A,B, with the same-sort/disjoint-sort convention. For equivariant
surjections tau:A→Q and sigma:B→R, put J=ker(tau), K=ker(sigma). If Theta is
an output pair orbital and (x0,y0) belongs to its pullback P, then

\[
 P=J;\bigl(G\cdot(x_0,y_0)\bigr);K.
\]

Prove the diversity restriction and partition assertions. Prove that this
restriction is empty exactly in the same-root-sort case with J=K=Id and
Theta the same-point graph of tau and sigma. This case can occur even when
Q and R are different output sort names. Every output orbital and every
kernel here is actual, and every product is equality-inclusive RAW.

## M3 — strong algebra and collision removal under SAP

Define a legal atomic triangle by an actual realization on **three pairwise
distinct real points**, even when all three sort labels agree. For diversity
menus A:i→j, B:j→k set

\[
 A*B=\{c:\exists a\in A\;\exists b\in B\;
                  (a,b,c)\text{ has such a realization}\}.
\]

Allow the empty set for Boolean bookkeeping; it is not a nonempty exact
menu. Prove triangle permutation/Peirce, monotonicity, union laws and converse
reversal directly. Use actual source SAP for compatible nonempty products,
associativity and typed Top absorption. Use symmetric same-sort orbitals for
loop-menu commutation. Keep all sort labels allowed to repeat.

For Set-Pasch glue two complete triangle witnesses over their **entire
common complete edge**. SAP makes the two off-edge vertices distinct, so
their diversity colour witnesses

\[
 (A*B)\cap(C*D)\ne\varnothing
 \ \Longrightarrow\ (\bar A*C)\cap(B*\bar D)\ne\varnothing.
\]

Prove supported-fork duplication, including X⊆{c}*{bar(c)}*X and P⊆P³ for
nonempty loop menus, with the actual sort typing in the source proof.

Derive infinite pointwise-stabilizer orbits outside any finite complete real
base: strongly amalgamate arbitrarily many copies of a one-point extension,
embed in the source and align the base by homogeneity. This is a theorem
from age-SAP and homogeneity, not a new orbit-infinitude axiom.

Use it to injectivize a homomorphism of a finite partial diversity diagram,
fixing any designated set on which it is already injective and avoiding a
finite forbidden set outside those fixed images. Process vertices one by
one; the stabilizer base at a step is the **set of current neighbour
images**, which need not arise from an injective neighbour list. Avoid the
entire current image when moving a point, so later moves preserve freshness.

Finally prove that a positive strong word profile equals the diversity guard
of its actual represented word relation. Delete genuine identity letters
before using this statement. An all-identity word has empty diversity guard;
it never becomes a strong identity menu. No CCO or NR2 is used in M3.

## M4 — a consumer and the coordination round trip

Create a separate consumer module which imports the shared public core,
rather than accessing implementation internals. On an actual finite span
whose two factors intersect exactly in the displayed common base,
define base-path menus as plain diversity subsets:

\[
 D_C(a,b)=\bigcap_{c\in C}
         \bigl(\{\operatorname{col}(a,c)\}*
               \{\operatorname{col}(c,b)\}\bigr),
 \qquad a,b\notin C,\quad a\ne b.
\]

Prove empty-base Top, typed converse, and preservation under induced factor
embeddings into another such span whose base map is **onto the whole
designated target base**.
Factor embeddings may add vertices outside that base. The product is that
of one fixed actual source, with literal colour names fixed by the maps.
This consumer tests products, finite intersections, distinctness guards and
the finite-map API together. It does not assert exact-menu membership,
selected-amalgam legality, arbitrary base-enlargement naturality or SIR.

Exercise same-sort repeated vertices and a genuinely cross-sort example in
compiled examples or proofs. Include a RAW singleton/identity example and a
STRONG one-diversity-colour example so an accidental common identity cannot
pass unnoticed. Reuse existing finite controls as mathematical guidance;
their Python success is not a substitute for the Lean proofs.

Complete the actual branch → checkpoint report → PR → author notification
round trip. Report a useful intermediate milestone if the API reveals a
mathematical obstruction. The first package tests this process as well as
the mathematics; no second project is started before acceptance.

## Acceptance checklist

1. Shared public core, all M2/M3 results and the M4 consumer compile and are
   proved, without unproved transitive dependencies or additional axioms.
2. Exact source-to-Lean map lists RAW C01–C05, STRONG C01–C05 and both named
   group-action exports, with their actual minimal hypotheses.
3. Report records representation choices, exported declarations, pinned
   versions, public file ownership boundaries and actual validation/audit
   commands with outcomes on a named commit. All intended files are built.
4. A second reader can follow the documented clean-checkout procedure; GitHub
   CI succeeds on the submitted commit and integration is checked afterward.
5. Mathematical feedback is explicit; remaining future provider obligations
   are not represented as proved source theorems.
6. The preparation project reviews the report and accepts an integration
   commit. The author then assigns the next substantial package.

Optional extra helpers are fine. Optional extra mathematical scope is not a
requirement for acceptance and should not delay the first working API.
