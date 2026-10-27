import CCO.PairHomogeneity

/-!
# RAW C01–C04 directly from the actual homogeneous finite complete source

These are the source-strength exports; the underlying elementary lemmas
retain weaker explicit group-action assumptions for independent reuse.
Homogeneity here is finite tuple extension of the *original* atomic
colouring. No SAP, CCO, NR2 or RAW Helly is assumed.
-/

universe u v w

namespace CCO.AtomicSource

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Every invariant original typed relation is exactly the union of
its actually occurring (optional) pair colours, logical diagonal
included. -/
theorem invariant_support_representation_of_homogeneous
    (H : HomogeneousSource S G) {i j : ι}
    (R : TRel X i j)
    (hInv : TRel.Invariant (G := G) R) :
    S.representedSupport (S.rawSupport R) = R :=
  S.rawSupport_represents_invariant R hInv
    (S.pair_homogeneous_of_homogeneous H)

/-- Typed atomic Peirce for the *actual* original fine-colour atoms.
Even the real equality atom `none` is covered on loop sorts when
it actually occurs. The quantified `hcReal` is needed to prevent
a vacuous left-hand side for a nonexistent optional pair colour. -/
theorem raw_atomic_peirce_of_homogeneous
    (H : HomogeneousSource S G) {i j k : ι}
    (a : Option (S.Atom i j)) (c : Option (S.Atom i k))
    (B : TRel X j k)
    (hcReal : ∃ x : X i, ∃ z : X k, S.colour x z = c)
    (hInvB : TRel.Invariant (G := G) B) :
    (∀ x z, S.rawAtomRel c x z →
      TRel.comp (S.rawAtomRel a) B x z) ↔
      ∃ x y, S.rawAtomRel a x y ∧
        TRel.comp (S.rawAtomRel c) (TRel.converse B) x y :=
  S.raw_atomic_peirce a c B hcReal
    (S.colourInvariant_of_homogeneous H)
    (S.pair_homogeneous_of_homogeneous H) hInvB

/-- Correctly typed and genuinely RAW Top absorption, proved from
original-sort transitivity rather than any CCO premise. -/
theorem raw_top_comp_of_homogeneous
    (H : HomogeneousSource S G) {i j k : ι}
    (R : TRel X j k)
    (hNonempty : TRel.Nonempty R)
    (hInv : TRel.Invariant (G := G) R) :
    TRel.comp (TRel.top X i j) R = TRel.top X i k :=
  TRel.top_comp_invariant (G := G) R hNonempty hInv
    (S.original_sort_transitive_of_homogeneous H k)

/-- Same-sort invariant equivalence compositions are their least common
invariant-free join; no claim is made for mixed sorts or distributivity
of the full original equivalence lattice. -/
theorem same_sort_join_of_homogeneous
    (H : HomogeneousSource S G) {i : ι}
    (E F : X i → X i → Prop)
    (hE : RawSymmetric.EquivRel E)
    (hF : RawSymmetric.EquivRel F)
    (invE : ∀ (g : G) x y, E x y → E (g • x) (g • y))
    (invF : ∀ (g : G) x y, F x y → F (g • x) (g • y)) :
    RawSymmetric.EquivRel (RawSymmetric.compose E F) ∧
    (∀ x y, E x y → RawSymmetric.compose E F x y) ∧
    (∀ x y, F x y → RawSymmetric.compose E F x y) ∧
    (∀ K : X i → X i → Prop, RawSymmetric.EquivRel K →
      (∀ x y, E x y → K x y) →
      (∀ x y, F x y → K x y) →
      ∀ x y, RawSymmetric.compose E F x y → K x y) :=
  RawSymmetric.comp_equivalences_is_join E F hE hF invE invF
    (S.pair_flip_of_homogeneous H)

end CCO.AtomicSource
