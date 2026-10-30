import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Set.Finite.Range

/-! The finite real union of two embeddings over their exact common base.
Only displayed base points are identified, independently of owner collisions. -/
universe u v w
namespace CCO.CloneSAP.FiniteUnion
variable {A : Type u} {B : Type v} {C : Type w} (s : C ↪ A) (t : C ↪ B)

def OffBase := {b : B // b ∉ Set.range t}
abbrev Union := A ⊕ OffBase t

def left : A ↪ Union (A := A) t := Function.Embedding.inl

noncomputable def rightFun (b : B) : Union (A := A) t := by
  classical
  exact if h : b ∈ Set.range t then .inl (s h.choose) else .inr ⟨b,h⟩

@[simp] theorem right_base (c : C) : rightFun s t (t c) = .inl (s c) := by
  classical
  unfold rightFun
  split_ifs with h
  · congr 2
    exact t.injective h.choose_spec
  · exact (h ⟨c,rfl⟩).elim

@[simp] theorem right_off (b : B) (hb : b ∉ Set.range t) :
    rightFun s t b = .inr ⟨b,hb⟩ := by
  classical
  simp only [rightFun,dif_neg hb]

noncomputable def right : B ↪ Union (A := A) t where
  toFun := rightFun s t
  inj' := by
    classical
    intro b b' he
    by_cases h : b ∈ Set.range t
    · obtain ⟨c,rfl⟩ := h
      by_cases h' : b' ∈ Set.range t
      · obtain ⟨c',rfl⟩ := h'
        simp only [right_base,Sum.inl.injEq] at he
        exact congrArg t (s.injective he)
      · rw [right_base,right_off _ _ b' h'] at he
        cases he
    · by_cases h' : b' ∈ Set.range t
      · obtain ⟨c',rfl⟩ := h'
        rw [right_off _ _ b h,right_base] at he
        cases he
      · rw [right_off _ _ b h,right_off _ _ b' h'] at he
        exact congrArg (fun z : OffBase t => z.val) (Sum.inr.inj he)

@[simp] theorem commute (c : C) : left t (s c) = right s t (t c) := by
  exact (right_base s t c).symm

theorem intersection (a : A) (b : B) (he : left t a = right s t b) :
    ∃ c, s c = a ∧ t c = b := by
  classical
  by_cases h : b ∈ Set.range t
  · obtain ⟨c,rfl⟩ := h
    change .inl a = rightFun s t (t c) at he
    rw [right_base] at he
    exact ⟨c,(Sum.inl.inj he).symm,rfl⟩
  · change .inl a = rightFun s t b at he
    rw [right_off _ _ b h] at he
    cases he

end CCO.CloneSAP.FiniteUnion
