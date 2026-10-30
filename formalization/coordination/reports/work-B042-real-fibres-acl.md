# B042 — actual real fibres, palette chains and real algebraicity

Actual implementation author: `/root/b042_finite/real_acl`. Base is accepted
main `1121b2016c7141ac432364b07c49c0ae31b18dbe`, source pin remains
`490c3f36d85db5a0b3ced0598e6c431825254ec5`. The selected source is
`sections/cco_finite_fibres.tex`, especially `cor:fibre-uniform-acl`.
This helper edits only `CCO/FiniteFibres/Real/` and this source map.

## Actual objects and selected dependencies

`Real.Aut S` is literally the full group of every original optional-colour
preserving permutation of the real carrier. `fullHomogeneous` derives its
finite homogeneity from any supplied original homogeneous action; it does
not replace the full group by a subgroup with additional orbits.

`originalLanguage` has exactly the old binary diversity names and no function
symbols or extra predicates. `relationNames` bijects its entire relation
signature with the original palette. Logical equality remains first-order
equality. Both `originalAutEquiv` and `languageAutToOriginal` identify all
automorphisms of this actual language with the above full colour group.

Only the accepted B009 C09/C10 providers are used for real fibre inheritance:
`fibre_orbit_eq`, `fibre_homogeneous` and `fibre_semanticCCO`. No proof invokes
the accepted later finite Hasse, finite-fibre-size, triangle-fullness,
globalisation or arbitrary-imaginary theorem. The existing provider files
retain their original imports, but the selected proof terms require only
homogeneity and original semantic CCO.

`spokes S A x hx` reads actual diversity colours to the displayed real
anchors. `orbitOver` uses the full original pointwise stabilizer. Its literal
equality with the actual realized `FibreSet` proves finite-orbit algebraicity
iff finite realized fibre. `fibreFormula` is an actual finite conjunction of
Mathlib first-order formulas in the original language with precisely those
real parameters. Formula naturality under every original automorphism proves
`usual_algebraic_iff`, including arbitrary quantified defining formulas.

The counting proof partitions the real carrier outside A by actual spoke
functions. Finite selected fibres form a finite dependent sum; the anchors
and that sum map onto real acl. The function type has cardinal `d^n` and
each finite fibre has cardinal at most `2^d` after the independent finite
target theorem is supplied. This gives the exact nonempty-base bound
`n + d^n * 2^d`. No tuple, hidden coordinate or arbitrary quotient is counted.

## Source map

All names below are under `CCO.FiniteFibres.Real`.

| Claim / definition | Actual receiving construction or proof |
|---|---|
| D08 | `RealHull.Geometry.InducedAtom`, `fibre_palette_card_le` |
| D09/D11 | `spokes`, `spokes_colour`, `fibrePoint`, `SpokeType`, `spoke_type_count` |
| D10 | `Aut`, `orbitOver`, `acl`, `originalAutEquiv`, `languageAutToOriginal` |
| C29 | `orbit_eq_fibre`, `algebraic_iff_finite_fibre`, `fibreFormula_realize`, `fibre_definable`, `definable_invariant`, `usual_algebraic_iff` |
| C30 | `fibre_source_properties`, using only the actual selected C09/C10 providers |
| C31 | `actual_pair_orbit`, `invariant_colour` |
| C32/C33 input | Independent finite-target/group support; no old finite Hasse theorem is used here |
| C34 | `InvariantChain.increment`, `increment_atom_ne`, `increment_atom_injective`, `length_le_palette` |
| C35 | `power_bound_of_chain`, `finite_fibre_power` after the independently proved generic finite cardinal theorem |
| C36 | `SpokeType`, `spoke_type_count`, `finite_type_count` |
| C37 | `acl_eq_anchor_union_finite_fibres`, `fibre_disjoint`, `coverPoint_surjective` |
| C38 | `cover_card`, `acl_card_bound`, `uniform_real_bound` |
| C39 | `empty_orbit`, `empty_acl_infinite` |
| C40 | `empty_finite_power`, `acl_finite_source` |
| C41 | `real_source_package`, with its one generic finite-target input discharged in the final B042 owner export |
| C42 | `subsingleton_of_zero_palette`, `no_outside_of_zero_palette`, `zero_palette_singleton` |
| C43 | `exponent_le_of_card_bound`, independent of homogeneity and colour-orbital recognition |

`InvariantChain` ranges over ALL actual full-group invariant equivalences,
not merely exact kernels. Every strict adjacent step has an actual pair in
its set difference. Pair homogeneity turns its named atom into a whole
orbit; monotonicity makes different step atoms distinct. Thus its step
count is bounded by the original palette without any CCO or finite Hasse
premise. `power_bound_of_chain` combines the source's telescoping size with
this explicit named-colour bound. The separate C43 theorem derives the
exponent bound directly from a bit-code cardinal bound.

## Generic finite-target seam and final assembly

`FiniteAtomicCard.{v,w}` is a transparent statement of exactly the independently
proved finite-target cardinal theorem, for arbitrary finite inhabited
one-sort `AtomicSource`, homogeneous action and semantic homomorphic CCO.
It asserts `card F = 2^m` with `m <= card (T.Atom () ())`. It is neither
an axiom nor a new source hypothesis. The generic local reuse lemmas
`finite_fibre_power`, `uniform_real_bound`, `empty_finite_power` and
`real_source_package` take that theorem as an explicit argument. The final
B042 source export requires an actual proof of this argument from the
generic finite-target theorem; this helper does not certify that separate
group/finite-target branch. A final export leaving this argument open would
be an unfinished provider.

The empty-base branches never call the spoke-vector bound. Infinite original
M has empty real acl; finite inhabited M uses the finite-target theorem
directly. The zero-palette source is a singleton. No `0^0` convention is
required by these source conclusions. Countability and SAP are absent.

## Validation and provenance

All five helper Lean modules and the full source consumer closure passed
`lake build CCO.FiniteFibres.Real.Source` under the pinned Lean 4.34.1,
unchanged manifest and existing private physical build slot. The final
incremental closure had 1120 jobs; only actual changed helper modules were
compiled after the initial accepted dependency closure was materialized.
No broad receiving pipeline, tests or axiom audit was repeated locally.
No broad Mathlib/Tactic import, sorry/admit/new axiom, source/contract change,
accepted API change or unaccepted B041 dependency was introduced.

Actual external PR/main CI/audit and separate non-author final source review
remain the coordinator's gates and are not asserted by this helper receipt.
