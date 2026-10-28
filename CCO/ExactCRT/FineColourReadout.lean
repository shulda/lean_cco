import CCO.ExactCRT.ExactLattice

/-! C18: two-factor fine-colour readout is a RAW meet/product theorem,
separate from the abstract set CRT. Logical equality atoms are included. -/
universe u v w t
namespace CCO.ExactCRT
open RawExact
open ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{u,v,max u v,w} S)

/-- The exact two-factor equation K;a = (E;a)∩(F;a), including a=Id.
It uses source RAW distribution, and no CRT/distributive-lattice theorem. -/
theorem two_factor_colour_readout {i : ι} (E F : ExactEq S H cco i)
    (a : Option (S.Atom i i)) :
    TRel.comp (E.val ⊓ F.val).r (S.rawAtomRel a) =
      (fun x y => TRel.comp E.val.r (S.rawAtomRel a) x y ∧
        TRel.comp F.val.r (S.rawAtomRel a) x y) := by
  obtain ⟨D, hD⟩ := E.property
  obtain ⟨P, hP⟩ := F.property
  obtain ⟨A, hA⟩ := optional_original_atom_exact S a
  have hMeet : (fun x y => ∀ d, d ∈ [D, P] → evaluate S d.words x y) =
      (E.val ⊓ F.val).r := by
    funext x y
    apply propext
    change (∀ d, d ∈ [D, P] → evaluate S d.words x y) ↔ E.val x y ∧ F.val x y
    simp [hD, hP]
  have hn : TRel.Nonempty (fun x y => ∀ d, d ∈ [D, P] → evaluate S d.words x y) := by
    rw [hMeet]
    obtain ⟨x⟩ := S.nonemptySort i
    exact ⟨x, x, E.val.refl x, F.val.refl x⟩
  have h := comp_exact_meet_left_of_CCO S H cco [D, P] hn A
  rw [hMeet, hA] at h
  refine h.trans ?_
  funext x y
  apply propext
  simp [hD, hP]

/-- Same-sort commutation identifies the colour readout with actual
saturated quotient blocks. It does not assert that the real relation is
functional, nor that finite quotient maps lift to ambient automorphisms. -/
theorem exact_equivalence_saturation_reduces {i : ι} (E : ExactEq S H cco i)
    (a : Option (S.Atom i i)) :
    saturate E.val.r (S.rawAtomRel a) E.val.r =
      TRel.comp E.val.r (S.rawAtomRel a) :=
  invariant_equiv_saturation_reduces E.val.r (S.rawAtomRel a)
    ⟨E.val.refl, fun _ _ h => E.val.symm h, fun _ _ _ h k => E.val.trans h k⟩
    (colourInvariant_groupInvariant S H (isExactEq_colourInvariant S H E.property))
    (S.rawAtomRel_invariant a (S.colourInvariant_of_homogeneous H))
    (S.pair_flip_of_homogeneous H)

/-- Literal fine/coarse saturated-block equation, an independent
fine-colour consumer rather than a set-level CRT corollary. -/
theorem two_factor_saturated_colour_readout {i : ι} (E F : ExactEq S H cco i)
    (a : Option (S.Atom i i)) :
    saturate (E.val ⊓ F.val).r (S.rawAtomRel a) (E.val ⊓ F.val).r =
      (fun x y => saturate E.val.r (S.rawAtomRel a) E.val.r x y ∧
        saturate F.val.r (S.rawAtomRel a) F.val.r x y) := by
  change saturate (E ⊓ F).val.r (S.rawAtomRel a) (E ⊓ F).val.r = _
  rw [exact_equivalence_saturation_reduces S H cco (E ⊓ F) a,
    exact_equivalence_saturation_reduces S H cco E a,
    exact_equivalence_saturation_reduces S H cco F a]
  exact two_factor_colour_readout S H cco E F a

end CCO.ExactCRT
