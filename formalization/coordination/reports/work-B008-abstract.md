# B008 abstract CRT and finite order implementation

Actual author: `/root/b008_crt/abstract_crt`. Source pin
`490c3f36d85db5a0b3ced0598e6c431825254ec5`. No source contract or accepted
API was changed. This is implementation authorship, not independent review.

The six modules under `CCO/ExactCRT/Abstract*` and `FiniteOrder.lean` prove
C01–10 and C15–17 independently of all CCO/RAW/SAP/group-action providers.
They use only actual `Setoid` equivalences and their quotient sets, a binary
`Sublattice (Setoid A)` and actual represented commutation. No ambient equality
or universal equivalence is required in that sublattice.

- C01: `productSetoid`, `join_eq_comp`, `class_intersection_iff_join` and
  `quotient_images_eq_iff` identify the represented product, ambient join,
  class intersections and equality of actual quotient images.
- C02–03: `inf_sup_le_of_helly` is the actual three-class argument;
  `distribLattice_of_helly` derives the dual law. `classHelly_of_distrib`
  proves the finite induction with a nonempty internal finite meet and
  separate zero/one cases. `distributive_iff_classHelly` states the equivalence.
  `Distributive` uses the inherited binary sublattice operations; this avoids
  a different arbitrary typeclass instance changing those operations.
- C04–07: `coordinates_kernel`, `coordinates_injective`,
  `compatible_iff_pairwise`, `compatibleCoordinates_surjective`, `crtEquiv`,
  `classHelly_of_finiteCRT` and `helly_iff_finiteCRT`. Compatibility is equality
  in every actual ambient join quotient. The converse assumes CRT only for
  nonempty finite families, and uses inhabitedness for the empty class family.
  Families are `Fin n` in the Helly definition; `classHelly_finite` reindexes
  arbitrary finite types in an independent universe.
- C08–10: `join_irreducible_prime`, `join_irreducible_finite_prime`,
  `irreducible_decomposition`, `birkhoff`, `mem_birkhoff` and
  `birkhoff_inverse`. The exact matching pinned Mathlib theorems
  `SupIrred.supPrime`, `exists_supIrred_decomposition` and
  `OrderIso.lowerSetSupIrred` are reused as explicitly permitted in N04.
  Their source has been read: `SupIrred` excludes minimal elements and is
  equivalent here to nonzero binary join-irreducibility; decomposition is
  actual well-founded finite splitting; Birkhoff's forward map is
  `{p | p.val ≤ a}` and inverse is the finite join of the downset. These
  formulas and nonzero convention are retained as public theorem wrappers.
  `no_irreducibles_of_subsingleton` proves the one-element/empty-poset boundary.
- C15–16: `binary_meet_irreducible_prime`, `selected_meet_coordinate`,
  `selected_meet_coordinate_of_infIrred` and `selected_coordinate_image`.
  The list is explicitly nonempty and may repeat arbitrary coordinates.
  The last theorem supplies a surjective actual quotient map with the
  prescribed projection formula; it asserts no ambient action lifting.
- C17: `fibreProductEquiv` is the actual two-factor fibre-product bijection,
  proved separately using only represented commutation.

`empty_coordinates_bijective` and `one_coordinates_surjective` are downstream
boundary consumers. The empty tuple uses the AMBIENT top kernel, whether or
not top belongs to the binary sublattice. All public modules must be imported
by the B008 owner from `CCO.lean`.

Local verification on pinned Lean 4.34.1: `lake build
CCO.ExactCRT.AbstractCoordinates` succeeds (812 jobs). Targeted imports only;
no `sorry`, new axiom, classical result packaged as an unproved provider or
mathematical source hypothesis occurs. Whole-project/root import closure,
official axiom audit, independent review and exact remote/main CI are owned
by the B008 owner/coordinator and are not asserted by this helper report.

## Actual source instance C13–14

The same helper additionally authored `CCO/ExactCRT/SourceLattice.lean`
after importing the owner's compiled `ExactLattice.lean` (source leaf
`02eba1a`). `exact_commutes` and `exact_classHelly` genuinely instantiate
every abstract premise from the original homogeneous CCO source;
`exactDistribLattice`, `exactCRT`, `exactCRT_real_representative` and
`exactBirkhoff` are the resulting actual exports. `mem_exactBirkhoff` and
`exactBirkhoff_inverse` keep the literal forward downset and inverse join.

`exact_selected_coordinate_image`, `exactFibreProduct`, `exact_empty_CRT`,
`exact_repeated_coordinates` and `exact_singleton_irreducibles_empty` are
actual source/boundary consumers. Reusing the existing finite-palette
injection and represented algebra of the full `ColourEq` type imports
neither a Hasse theorem nor a finite-index premise. No SAP, countability or
full invariant-lattice distributivity is asserted or assumed. The actual
instance needs only original homogeneity and semantic CCO.

Local `lake build CCO.ExactCRT.SourceLattice` succeeds (1118 jobs). No
whole-project or final integration audit is claimed here.
