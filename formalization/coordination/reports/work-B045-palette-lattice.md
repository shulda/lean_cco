# B045 independent palette lattice — root contribution

Source pin: `490c3f36d85db5a0b3ced0598e6c431825254ec5`.
Read actual `sections/ramsey_preferred_support.tex`, selected
`prop:lattice-interface` / `eq:join-composition`, and clone_sap N06/N07.
Actual author: `/root`; no reviewer authored or designed this code.

All declarations below are relative to `CCO.CloneSAP.Lattice`.

| Contract | Actual implementation |
|---|---|
| D07, C28 | `Palettes.lean`: `relation`, `Palette`, `paletteOrderIso`; palettes contain only diversity atoms and logical equality is separate. Actual occurrence proves uniqueness. |
| C27 | `Definability.lean`: `colour_iff_pair_orbit`, from the real finite two-point homogeneity theorem. |
| C28 | `namedAut` proves preservation of the actual finite named first-order language; `formula_invariant` uses real first-order semantics for arbitrary quantified formulas. `palette_has_formula`, `definable_equivalence_palette`, `invariant_equivalence_palette` give both definability directions and unique actual palettes. |
| C29 | `Finite (Palette S i)`, `palette_card_bound`, `bottom_eq_empty`, `top_eq_univ`, `lattice`, `meet_eq_inter`; finite lattice order is literal palette inclusion. Empty diversity palettes are allowed. |
| C30 | `degenerate_reverse`, including all three equality cases of the intermediate witness. |
| C31–C33, JC | `composition_commutes`, `join_composition`, with the independently proved actual original endpoint swap. Products include logical diagonals and are least upper equivalences; no union-of-palettes join is claimed. |
| D08 | `relativeClassEquiv` gives actual uniform relative-class bijections without a finite-index assumption. |
| C34 | `DirectedBoundary.lean`: all six actual S3 differences, equality iff identity, actual occurrence and translation preservation; `homogeneous` extends every partial tuple map to a left translation. Actual invariant setoids E/F from the two transpositions satisfy `ordered_product_witness` and `products_do_not_commute`. No symmetry or CCO is attributed to this directed boundary. |

The positive result assumes only the original finite atomic source and its
homogeneity. It does not assume AP, SAP, CCO, countability, triangle
constraints, a clone construction, or a separate one-point extension oracle.
The original named formula construction and actual same-sort orbital algebra
are reused from accepted modules with their weaker hypotheses visible.

Pinned local Lean 4.34.1, bundled Lake and unchanged manifest:
`lake build CCO.CloneSAP.Lattice.Definability CCO.CloneSAP.Lattice.DirectedBoundary`
passed (1,519 jobs; incremental dependencies reused). This is scoped local
compile evidence; exact public-head/main CI and the transitive standard-three
axiom audit remain whole-batch gates. No new axiom or native-decision shortcut
is introduced; S3 computations are checked by kernel `decide`.
