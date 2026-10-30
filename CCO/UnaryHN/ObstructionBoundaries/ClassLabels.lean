import CCO.UnaryHN.ObstructionBoundaries.Basic

/-! Equivalence-class labels for the genuine amalgam. Classes meeting the
common root receive the SAME root quotient label; other classes retain a
side tag. No equivalence class on either side is merged improperly. -/
universe u
namespace CCO.UnaryHN.Native.ObstructionBoundaries
open StructuralRamsey
open StructuralRamsey.Structure

theorem embedding_equivalence_iff {H V : Type u} {P : Setoid H} {E : Setoid V}
    (e : Embedding (network P) (network E)) (x y : H) :
    E.r (e x) (e y) ↔ P.r x y := by
  by_cases hxy : x = y
  · subst y
    exact ⟨fun _ => P.refl _, fun _ => E.refl _⟩
  · have h := e.map_rel_iff false ![x, y]
    change (E.r (e x) (e y) ∧ e x ≠ e y) ↔ P.r x y ∧ x ≠ y at h
    exact ⟨fun he => ((h.mp ⟨he, e.injective.ne hxy⟩).1),
      fun hp => (h.mpr ⟨hp, hxy⟩).1⟩

noncomputable def classLabel {H V : Type u} (P : Setoid H) (E : Setoid V)
    (e : H → V) (x : V) : Quotient P ⊕ Quotient E := by
  classical
  exact if h : ∃ r, E.r x (e r) then .inl (Quotient.mk P (Classical.choose h))
    else .inr (Quotient.mk E x)

theorem classLabel_eq_iff {H V : Type u} (P : Setoid H) (E : Setoid V)
    (e : H → V) (hE : ∀ x y, E.r (e x) (e y) ↔ P.r x y) (x y : V) :
    classLabel P E e x = classLabel P E e y ↔ E.r x y := by
  classical
  by_cases hx : ∃ r, E.r x (e r)
  · by_cases hy : ∃ r, E.r y (e r)
    · simp only [classLabel, dif_pos hx, dif_pos hy, Sum.inl.injEq]
      constructor
      · intro h
        exact E.trans (Classical.choose_spec hx)
          (E.trans ((hE _ _).mpr (Quotient.exact h)) (E.symm (Classical.choose_spec hy)))
      · intro h
        apply Quotient.sound
        apply (hE _ _).mp
        exact E.trans (E.symm (Classical.choose_spec hx))
          (E.trans h (Classical.choose_spec hy))
    · simp only [classLabel, dif_pos hx, dif_neg hy, Sum.inl_ne_inr, false_iff]
      intro h
      exact hy ⟨Classical.choose hx, E.trans (E.symm h) (Classical.choose_spec hx)⟩
  · by_cases hy : ∃ r, E.r y (e r)
    · simp only [classLabel, dif_neg hx, dif_pos hy, Sum.inr_ne_inl, false_iff]
      intro h
      exact hx ⟨Classical.choose hy, E.trans h (Classical.choose_spec hy)⟩
    · simp only [classLabel, dif_neg hx, dif_neg hy, Sum.inr.injEq]
      exact ⟨Quotient.exact, Quotient.sound⟩

theorem classLabel_root {H V : Type u} (P : Setoid H) (E : Setoid V)
    (e : H → V) (hE : ∀ x y, E.r (e x) (e y) ↔ P.r x y) (r : H) :
    classLabel P E e (e r) = .inl (Quotient.mk P r) := by
  classical
  have h : ∃ s, E.r (e r) (e s) := ⟨r, E.refl _⟩
  simp only [classLabel, dif_pos h]
  apply congrArg Sum.inl
  apply Quotient.sound
  exact (hE _ _).mp (E.symm (Classical.choose_spec h))

inductive AmalgamLabel (H V W : Type u)
  | root : H → AmalgamLabel H V W
  | left : V → AmalgamLabel H V W
  | right : W → AmalgamLabel H V W

def leftLabelMap {H V W : Type u} : H ⊕ V → AmalgamLabel H V W
  | .inl r => .root r
  | .inr a => .left a

def rightLabelMap {H V W : Type u} : H ⊕ W → AmalgamLabel H V W
  | .inl r => .root r
  | .inr b => .right b

theorem leftLabelMap_injective {H V W : Type u} :
    Function.Injective (@leftLabelMap H V W) := by
  intro x y h
  cases x <;> cases y <;> simp_all [leftLabelMap]

theorem rightLabelMap_injective {H V W : Type u} :
    Function.Injective (@rightLabelMap H V W) := by
  intro x y h
  cases x <;> cases y <;> simp_all [rightLabelMap]

end CCO.UnaryHN.Native.ObstructionBoundaries
