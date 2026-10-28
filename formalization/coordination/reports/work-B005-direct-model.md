# B005 direct real two-sheet branch

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Author: `/root/b005_positive/direct_model`.
Basis: accepted main `21381f6095d3b2787e3e248e5ea244180a66f06f`.

This branch implements C20 and C22–25 in the literal old real language.
C21 (the direct signed-cycle CCO proof) is separately implemented by the
actual contributor `/root/direct_cco`, with this same source API. The final
positive-relative headline must combine that theorem rather than assume CCO.

## Actual source and precise premises

`CCO.SIR.Positive.Direct.Point` is `ℕ × Bool × ℕ`, not an abstract provider.
`source` has one named sort and the three diversity colours `e,d,n`:
real equality is `none`, equal parent-and-sheet distinct points have `e`,
same-parent different-sheet points have `d`, and different parents have `n`.
Neither parents nor individual sheets are named predicates in the language.
`Aut` is the full subgroup of real permutations preserving these old colours.
All results below have no model/homogeneity/SAP/HS/NR2/existence provider.

| Claim | Compiled exports and proof |
|---|---|
| C20 actual source | `Direct/Source.lean`: `source`, `colour_none/e/d/n`, original equality-inclusive `E` and `F`, and their setoids. |
| C20 homogeneity | `Direct/Homogeneity.lean`: `finite_extension` for every finite tuple, including repeated points; finite equality-kernel tuple maps extend by actual permutations. Parent, unlabelled-sheet and fibre permutations assemble into a genuine colour-preserving real permutation. `homogeneous` is the actual `HomogeneousSource source Aut`. |
| C20 SAP | `Direct/Amalgamation.lean`: `strongAmalgamation : AgeSAP source`. Align arbitrary base embeddings by real homogeneity, move the left side over the fixed actual right base, and use the proved real overlap clause to exclude every new collision. Points remain distinct also inside an anchored parent. |
| C20 finite age | `Direct/Geometry.lean`: `finite_age_two_sheets` and `finite_age_realization`. Every finite nested pair of equivalences `e≤f` with at most two lower classes in each upper class embeds into the literal real carrier; an age object need not represent both sheets. |
| C20 full invariant lattice | `full_colour_lattice`, `full_invariant_lattice`, `full_lattice_strict`: ALL invariant setoids are exactly `Id<E<F<Top`. An included d orbital forces e by transitivity; an included n orbital forces Top via a fresh parent. Every proper full invariant equivalence has an infinite actual global quotient (`infinite_global_quotient`). |
| C22 direct relation and existence | `Direct/Fresh.lean`: `Independent`, `independent_existence`. The base is fixed pointwise. Unanchored parents move above all finite right/base parents and off-base indices move above every finite right/base index, preserving all old colours. Homogeneity extends this literal finite target map. |
| C22 invariance/symmetry/normalization | `Direct/Independence.lean`: `independent_normalization`, `independent_transport`, `independent_invariance`, `independent_symmetry`. These are actual old-language automorphisms. |
| C23 both transitivity directions | `independent_restriction`, `independent_transitivity`. A shared unanchored parent at the old base either meets B, contradicting the first independence assumption, or remains unanchored at B∪C, contradicting the second. Real equality overlap is handled separately. |
| C24 prescribed stationarity | `cross_colour`, `independent_stationarity`, `stationaryIndependence`. The two Boolean comparisons to an actual base anchor determine a cross sheet even when both are false (`bool_comparison`). The actual old finite union map is extended, fixing EVERY point of B∪C while agreeing with the prescribed map on A. `g` is arbitrary; homogeneity extends every prescribed old finite partial isomorphism to such a g. |
| C25 finite relative index | `relativeIndexTwo`, `sheetClassMap_bijective`, `sheetClassEquiv`, `actual_relative_index`: each actual quotient of a full F-class by E is explicitly equivalent to Bool, with literal index two. `infinite_sheet` exhibits infinitely many actual real points in every E-fibre. `violates_originalNR2` is proved for the original full condition. |

## Consumers and checks

`Direct/Consumers.lean` proves actual transitivity, the exact empty-base
characterization by n cross atoms (including equality separation), the
base-contained-side case, a concrete d-coloured anchored independent pair,
its dependence at the empty base, real fixed-copy existence and pointwise
stationarity. In particular the relation is the stated parent formula,
not a sufficient NR2/HS selector renamed as the direct model.

Each new file was compiled locally using the pinned Lean 4.34.1 and locked
manifest. The last increment `lake build CCO.SIR.Positive.Direct.Consumers`
completed successfully (1036 transitive jobs). No full B005 root/audit claim
is made by this partial-branch report: the batch owner adds all public imports,
combines C21, and owns the one final complete package build/audit and source map.
No source theorem, mathematical contract, toolchain or accepted API changed.
