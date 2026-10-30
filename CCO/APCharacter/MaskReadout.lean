import CCO.APCharacter.ActualMasks

/-! The literal mask is exactly the union of correct-character rigid arrows
and flexible nonrigid old atoms. Inactive labels are fixed, not free bits. -/
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace CCO.APCharacter
open RigidGroupoid.Geometry RigidGroupoid.Phase
noncomputable section
variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable {H : HomogeneousSource S G} {C : ExactCalculus S} {r : ι} {A : Kernel S r}
namespace SourcePhase
variable (P : SourcePhase S H C A)

theorem rigid_mask_iff (b c : Reached S A)
    (R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c))
    (x : X b.val) (y : X c.val) (hR : R.rel x y) (ε η : Bit) :
    letI := Reached.groupoid H C (A := A)
    P.allows (S.colour x y) ε η ↔
      P.validBit b.val ε ∧ P.validBit c.val η ∧ η = ε + P.character.value R := by
  letI := Reached.groupoid H C (A := A)
  constructor
  · intro h
    exact ⟨h.1,h.2.1,h.2.2 x y rfl b.property c.property R hR⟩
  · rintro ⟨hε,hη,hχ⟩
    apply (P.allows_actual_iff x y ε η).mpr
    refine ⟨hε,hη,?_⟩
    intro hi hj T hT
    have he : T = R := T.eq_of_common_real_pair H R hT hR
    exact he ▸ hχ

theorem active_mask_union (b c : Reached S A) (x : X b.val) (y : X c.val) (ε η : Bit) :
    letI := Reached.groupoid H C (A := A)
    P.allows (S.colour x y) ε η ↔ P.validBit b.val ε ∧ P.validBit c.val η ∧
      ((∃ R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c),
        R.rel x y ∧ η = ε + P.character.value R) ∨
       ¬∃ R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c), R.rel x y) := by
  letI := Reached.groupoid H C (A := A)
  constructor
  · intro h
    refine ⟨h.1,h.2.1,?_⟩
    by_cases hex : ∃ R : Arrow S (Reached.kernel H C b) (Reached.kernel H C c), R.rel x y
    · obtain ⟨R,hR⟩ := hex
      exact Or.inl ⟨R,hR,h.2.2 x y rfl b.property c.property R hR⟩
    · exact Or.inr hex
  · rintro ⟨hε,hη,h | hn⟩
    · obtain ⟨R,hR,hχ⟩ := h
      exact (P.rigid_mask_iff b c R x y hR ε η).mpr ⟨hε,hη,hχ⟩
    · apply (P.allows_actual_iff x y ε η).mpr
      exact ⟨hε,hη,fun hi hj R hR => False.elim (hn ⟨R,hR⟩)⟩

theorem inactive_masks_full {i j : ι} (ε η : Bit)
    (hv : P.validBit i ε) (hw : P.validBit j η)
    (inactive : ¬Nonempty (Bridge S A i) ∨ ¬Nonempty (Bridge S A j))
    (c : Option (S.Atom i j)) : P.allows c ε η := by
  refine ⟨hv,hw,?_⟩
  intro x y _ hi hj _ _
  exact False.elim (inactive.elim (fun h => h hi) (fun h => h hj))

theorem inactive_bit_unique {i : ι} (hi : ¬Nonempty (Bridge S A i))
    {ε η : Bit} (hε : P.validBit i ε) (hη : P.validBit i η) : ε = η :=
  (hε hi).trans (hη hi).symm

end SourcePhase
end
end CCO.APCharacter
