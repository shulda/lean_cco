# B038 actual relational collision unfolding

Source: `490c3f36d85db5a0b3ced0598e6c431825254ec5`,
`sections/foundational_sap_collision_unfolding.tex`,
`formalization/relational_completion/module.json` and `PROOF_NOTES.md`.
The mathematical package has no prerequisites. No B037 theorem is imported.

## Actual signature and principal result

`Relational.Language.Rel : ℕ → Type u` admits arbitrarily many relation
symbols of every finite arity, including nullary symbols. There are no
functions and no finite palette hypothesis. `Structure.induce` literally
restricts all relations to an arbitrary subset, with no closure condition.

`Structure.collision_unfolding` takes a finite source A, target U with genuine
finite induced homogeneity and actual strong amalgamation of its finite age,
and the GIVEN same-map homomorphism-embedding h. It constructs an injective
HE k. On ANY separately marked family S, whose old h restrictions are assumed
injective, it preserves the full induced target-image relation profiles.
`SameImageType.imageIso` constructs the actual isomorphism of h(S) onto k(S),
with the same source point correspondence. Reflection of SOURCE S is neither
assumed nor concluded. No joint image-union or fixed-position statement occurs.

`collision_unfolding_source` retains the source's countable target, finite
family and distinguished COMPLETE factors. Completeness is explicit data:
`Declarations.negative` is consistent with every positive A relation, and
`CompleteOn S` requires positive OR negative declarations on EVERY tuple in S,
including nullaries. `negative_iff_not_positive` checks its intended meaning.
The stronger core needs only actual h-injectivity on S; it forgets the
annotations and countability when constructing k. Thus no stronger source
reflection premise hides in the completeness marking.

## Claim map

| Claims | Actual Lean declarations and proof |
| --- | --- |
| C01 | `tuple_support_irreducible`: every positive tuple forces one free factor to contain its entire distinct-entry support. Arbitrary arity and repetitions are literal. |
| C02 | `IsHE.fibre_unique`, `IsHE.tuple_fibre_unique`: the GIVEN map is induced and injective on every irreducible support. |
| C03 | `injOn_fibre_unique`: only the separately assumed restriction injectivity is used. |
| C04–C05 | `induced_mem_age`, `inclusion`, `induce`: full target image and its FULL point deletion are actual age objects. |
| C06–C08 | `exists_induced_clone`: actual SAP of two full image copies over the whole deletion base; embed its finite age host in U, extend first-copy alignment to an actual automorphism, prove second point outside ALL old images. The resulting Embedding retains every positive and negative tuple. |
| C09 | `split`: precisely the selected source vertices move simultaneously; all occurrences of one vertex move together. |
| C10 | `IsHE.split.positive`: EVERY displayed positive tuple uses C01/C02, then the actual full clone; this is global positive preservation. |
| C11 | `split_restriction`, `split_embedsOn`, `IsHE.split.irreducible`: on each old induced piece the new map is literally unchanged or the clone composed with the old map. |
| C12 | `split_injOn`, `split_sameImageType`, `SameImageType.imageIso`: actual separate target-image invariants, requiring no source reflection. |
| C13 | `Collision.Counting`: actual unordered distinct equal-image pairs; exact binomial fibre counts, μsplit+t(r−t)=μold, strict decrease, all other fibres unchanged, image cardinality +1. |
| C14 | `collision_unfolding`: strong induction on that actual unordered collision count, with an actual fresh clone and singleton proper split at every noninjective step. Per-step image profiles compose to each ORIGINAL image. |
| C15 | `collision_unfolding_source`: actual finite-family source statement with explicit complete declarations and countability retained. |
| C16 | `already_injective` and the core's identity branch include empty/singleton sources; no symbol enumeration, signature finiteness or binary restriction is used anywhere. |

All relational boundary providers are now complete:

| Claims | Actual boundary proofs |
| --- | --- |
| C30 | `BoundariesAP.target` is Option ℕ with red iff none. `target_countable`, `target_homogeneous`, `target_ageAP`, `target_not_ageSAP` are proved for the actual structure. The homogeneity proof extends the actual finite partial blue bijection, augmented by the red point, to a permutation fixing none. `foldRed_HE`, `twoRed_no_injective_hom`, `counterexample` give the actual two-red-point HE with no injective positive replacement. |
| C31 | `Boundaries.isolated_isHE` treats any loop-free binary target and any injective map of two isolated source points. `isolated_not_embedding` uses an actual edge to refute global inducedness; `two_isolated_into_edge` gives the literal finite witness. This is a local universal edge adapter applicable inside the random graph; construction of the random graph itself is not claimed. |
| C32 | `Boundaries.collapsed_isHE` maps two pure-set points constantly into ℕ; `separate_singleton_image_iso` constructs an actual Iso for EACH protected singleton after injectivization. `joint_image_card_changes`, `joint_images_not_isomorphic`, `cannot_fix_all_old_positions` explicitly rule out the joint-union/literal-position strengthening. |
| C35 | `Boundaries.functional_deletion_not_closed` uses the actual Bool function constant true: deleting true retains false but loses its function value. This delimits the deletion proof, not unrelated unary injectivization theorems. |

The independent atomic C17–C29 and C33–C34 providers and their scope are mapped
in `work-B038-atomic-fullness.md` and `work-B038-atomic-boundaries.md`.

## Validation and current limits

All 23 new modules, including every boundary provider, are imported from
`CCO.lean` after the accepted prefix. Their complete SourceAssembly union
passed the narrow build under pinned Lean 4.34.1 (1291 jobs).
Mathematical freeze: `5e71e93a88ceb0f9ac7384b0dac216d753dd6f6f`. These are actual
source proofs, with no new axioms, sorry/admit or conditional clone/provider
callbacks. Whole-package build, transitive axiom audit, independent final
review, exact-head CI and actual resulting-main CI remain final gates.
The owner will run its ONE complete pipeline after B037 is accepted and its
main merged into this history. No pending sibling theorem is used by B038.
