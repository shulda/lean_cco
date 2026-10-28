# B016 abstract characters and phase seeds

Actual author: `/root/b016_phase/abstract_markings`. Initial scope:
rigid_groupoid C24–C30. The owner's follow-up assigns actual C31 integration
in the additional `ActualPhase.lean`, using the owner's separately proved
`SourceCharacter` and `ActualOrbitals` modules.
Pinned source: `490c3f36d85db5a0b3ced0598e6c431825254ec5`, actual
`sections/rigid_exact_groupoid_foundations.tex`, binary-character theorem and
finite-phase-extension lemma, with proof notes N07–N08.

| Claim | Constructed Lean export |
|---|---|
| C24 | `Abstract.detecting_character`: extend the nonzero vector's singleton to a basis and use its literal coordinate functional to obtain value one. The supplied module is a finite F2 vector space. |
| C25 | `normalizedConnectors`, `rootCoefficient`, `coefficient_reconstruct`, `coefficient_unique`, `connectedCharacter`, `connectedCharacter_root`: choose normalized paths from actual connectedness, cancel paths to obtain the unique root coefficient, and prove character additivity on composition. |
| C26 | `transported_nonidentity`, `transported_square`, `transported_independent`, `transported_character`: conjugation preserves a nontrivial involution, commutative root isotropy makes the path independent, and character one transports without any dominance premise. |
| C27 | `Abstract.exists_marking`: the actual tagged point orbit setoid, one chosen seed per orbit, the unique transporting arrow and literal propagation construct one global compatible bit function. |
| C28 | `rigid_difference`, `different_orbits_both_differences`: each rigid arrow forces its character difference in every marking; distinct point orbits can receive either difference across suitable global choices by shifting only one orbit. |
| C29 | `finite_restriction`: restriction of a global marking to any literal finite tagged-point set. Source pullbacks and reduct-surjectivity are separate C31 consumers. |
| C30 | `finite_seed_extension_iff`: for bits on the actual finite-point subtype, global extension is equivalent to every transporting pair equation. `empty_seed_extends` and `singleton_extends` are explicit boundary consumers. |
| C31 | `actual_action_free`, `actual_global_marking`, `actual_rigid_difference`, `actual_nonrigid_both_differences`, `actual_finite_seed_extension_iff`: all are instantiated on the literal original-source reached kernel quotient sets and actual bridge arrows. `originalMarking`, its gate-constant/representative-consistency/arrow-equation lemmas and `finite_original_reduct_surjective` pull bits back to ALL original sorts and every actual finite original induced structure. `standing_source_phase` and `standing_finite_marked_reduct` construct both the detecting character and markings from the original H+CCO source, retaining the explicit countability convention and distinguished nonidentity arrow. |

Namespace: `CCO.RigidGroupoid.Phase.Abstract`. Public files are
`AbstractCharacter.lean`, `AbstractMarkings.lean`, `AbstractSeeds.lean` under
`CCO/RigidGroupoid/Phase/`, followed by actual-source `ActualPhase.lean` in
namespace `CCO.RigidGroupoid.Phase`. The owner adds their root imports.

The seed layer assumes only a functor from a groupoid to actual point sets,
freeness on each source point, and a given additive character. It does not
assume finite or connected object sets, elementary abelian isotropy, a
distinguished involution, or any original-source geometry. Its stronger
arbitrary-prescribed-subset lemma uses the same orbit-seed construction;
the allocated finite result is the literal finite-subtype wrapper. Equality
of repeated presentations must therefore descend to a genuine function on
the actual point set. No higher-arity condition is inserted.

The character layer is pure groupoid/finite linear algebra. Source orbitals,
exactness, CCO, SAP, dominance, definability, compactness, global automorphisms,
and moving-owner kernel projections are neither premises nor conclusions of
the abstract seed construction. In particular, changing an orbit seed gives
existence across global markings, not both differences in one fixed marking.

Validation: pinned Lean 4.34.1, locked manifest, independent local build
directory and shared read-only package cache. Final targeted build
`lake build CCO.RigidGroupoid.Phase.AbstractSeeds` succeeded, 1405 jobs,
covering all three changed public modules and dependencies. Only two existing
Mathlib alias deprecation warnings (`if_pos`/`if_neg`) remain. No sorry,
admit, new axiom, or contract/toolchain/manifest/shared API change is present.
The owning batch performs the one final whole-project build, official audit
and current-source/artifact checks; this helper does not duplicate them.

The follow-up actual C31 target
`lake build CCO.RigidGroupoid.Phase.ActualPhase` succeeded, 1758 jobs.
Its action freeness is proved directly from the accepted actual quotient
bijections, and original H+CCO supplies the exact calculus. No character,
free-action, finite-isotropy, quotient-homogeneity or global-marking provider
is added as an unproved source premise. The distinguished nonidentity arrow
remains explicit at a chosen actual reached object. The finite seed iff takes
bits on literal quotient points, and the real-representative lemma rules out
conflicting bits on equal gate classes. Unreached named sorts receive zero
bits; no claim about their rigid equations is invented. The actual finite
reduct consumer returns unary bits on the SAME original `FiniteInduced D`,
including empty D; it claims no marked AP/SAP/CCO or moving-owner action.
