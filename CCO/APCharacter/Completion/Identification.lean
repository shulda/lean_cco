import CCO.APCharacter.Completion.Identity
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite

/-! The literal finite carrier used for an identity contraction. Its fibres,
sorts, labels and strict vertex-count decrease are proved explicitly. -/
universe u v w z
namespace CCO.APCharacter.Completion
variable {V : Type z} (x y : V) (hxy : x ≠ y)
abbrev Identified := {v : V // v ≠ y}

noncomputable def identify (v : V) : Identified y := by
  classical
  exact if h : v = y then ⟨x,hxy⟩ else ⟨v,h⟩

@[simp] theorem identify_y : identify x y hxy y = ⟨x,hxy⟩ := by
  classical
  simp [identify]

@[simp] theorem identify_of_ne (v : V) (hv : v ≠ y) :
    identify x y hxy v = ⟨v,hv⟩ := by
  classical
  simp [identify,hv]

theorem identify_onto : Function.Surjective (identify x y hxy) := by
  rintro ⟨v,hv⟩
  exact ⟨v,identify_of_ne x y hxy v hv⟩

theorem identify_fibres (a b : V) :
    identify x y hxy a = identify x y hxy b ↔
      a = b ∨ (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
  classical
  by_cases ha : a = y <;> by_cases hb : b = y
  · subst a; subst b; simp
  · subst a
    simp only [identify_y,identify_of_ne x y hxy b hb,Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inr (Or.inr ⟨True.intro,h.symm⟩)
    · rintro (h | ⟨h,_⟩ | ⟨_,h⟩)
      · exact False.elim (hb h.symm)
      · exact False.elim (hxy h.symm)
      · exact h.symm
  · subst b
    simp only [identify_y,identify_of_ne x y hxy a ha,Subtype.mk.injEq]
    constructor
    · intro h; exact Or.inr (Or.inl ⟨h,True.intro⟩)
    · rintro (h | ⟨h,_⟩ | ⟨h,_⟩)
      · exact False.elim (ha h)
      · exact h
      · exact False.elim (ha h)
  · rw [identify_of_ne x y hxy a ha,identify_of_ne x y hxy b hb]
    simp only [Subtype.mk.injEq]
    constructor
    · exact Or.inl
    · rintro (h | ⟨_,h⟩ | ⟨h,_⟩)
      · exact h
      · exact False.elim (hb h)
      · exact False.elim (ha h)

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable (D : PartialDiagram S V)

theorem identify_sorts (same : D.vertexSort x = D.vertexSort y) (a : V) :
    D.vertexSort (identify x y hxy a).val = D.vertexSort a := by
  classical
  by_cases h : a = y
  · subst a; simpa only [identify_y] using same
  · rw [identify_of_ne x y hxy a h]

theorem identify_bits {B : Type*} (bits : V → B) (same : bits x = bits y) (a : V) :
    bits (identify x y hxy a).val = bits a := by
  classical
  by_cases h : a = y
  · subst a; simpa only [identify_y] using same
  · rw [identify_of_ne x y hxy a h]

/-- C32: a real identity contraction lowers the FIRST coordinate of the
completion measure, regardless of its effect on missing pairs. -/
theorem identify_card_lt [Finite V] : Nat.card (Identified y) < Nat.card V := by
  classical
  letI := Fintype.ofFinite V
  have h := Fintype.card_lt_of_injective_not_surjective
    (f := (Subtype.val : Identified y → V)) Subtype.val_injective (by
      intro h
      obtain ⟨a,ha⟩ := h y
      exact a.property ha)
  simpa only [Nat.card_eq_fintype_card] using h

end CCO.APCharacter.Completion
