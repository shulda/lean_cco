import CCO.ResetOrder.Counterexample.Successor
import Mathlib.Data.Sum.Order

/-! Disjoint unions of whole P-components give actual joint embeddings at
all three levels; the successor maps stay inside their original components. -/
universe u v
namespace CCO.ResetOrder.Counterexample

private def sumRel {X : Type u} {Y : Type v} (r : X → X → Prop) (s : Y → Y → Prop) :
    X ⊕ Y → X ⊕ Y → Prop
  | .inl x, .inl y => r x y
  | .inr x, .inr y => s x y
  | _, _ => False

private def sumSetoid {X : Type u} {Y : Type v} (r : Setoid X) (s : Setoid Y) : Setoid (X ⊕ Y) where
  r := sumRel r.r s.r
  iseqv := ⟨by
    rintro (x | x)
    · exact r.refl x
    · exact s.refl x,
    by
    rintro (x | x) (y | y) h
    · exact r.symm h
    · exact False.elim h
    · exact False.elim h
    · exact s.symm h,
    by
    rintro (x | x) (y | y) (z | z) h₁ h₂
    · exact r.trans h₁ h₂
    · exact False.elim h₂
    · exact False.elim h₁
    · exact False.elim h₁
    · exact False.elim h₁
    · exact False.elim h₁
    · exact False.elim h₂
    · exact s.trans h₁ h₂⟩

namespace Nested
variable {X : Type u} {Y : Type v} (A : Nested X) (B : Nested Y)

def jointBase : Nested (X ⊕ Y) where
  P := sumSetoid A.P B.P
  Q := sumSetoid A.Q B.Q
  refine := by
    rintro (x | x) (y | y) h
    · exact A.refine h
    · exact False.elim h
    · exact False.elim h
    · exact B.refine h

def jointLeft : Embedding A (A.jointBase B) where
  point := Sum.inl
  injective := Sum.inl_injective
  p_iff _ _ := Iff.rfl
  q_iff _ _ := Iff.rfl

def jointRight : Embedding B (A.jointBase B) where
  point := Sum.inr
  injective := Sum.inr_injective
  p_iff _ _ := Iff.rfl
  q_iff _ _ := Iff.rfl

namespace ConvexOrder
variable {A B} (a : ConvexOrder A) (b : ConvexOrder B)

def jointOrder : ConvexOrder (A.jointBase B) := by
  letI := a.order
  letI := b.order
  refine {
    order := LinearOrder.lift' (toLex : X ⊕ Y → X ⊕ₗ Y) toLex.injective
    convexP := ?_
    convexQ := ?_ }
  all_goals
    rintro (x | x) (y | y) (z | z) h₁ h₂ hR
    · first
      | exact a.convexP (Sum.Lex.inl_le_inl_iff.mp h₁) (Sum.Lex.inl_le_inl_iff.mp h₂) hR
      | exact a.convexQ (Sum.Lex.inl_le_inl_iff.mp h₁) (Sum.Lex.inl_le_inl_iff.mp h₂) hR
    · exact False.elim hR
    · exact False.elim (Sum.Lex.not_inr_le_inl h₂)
    · exact False.elim hR
    · exact False.elim hR
    · exact False.elim (Sum.Lex.not_inr_le_inl h₁)
    · exact False.elim hR
    · first
      | exact b.convexP (Sum.Lex.inr_le_inr_iff.mp h₁) (Sum.Lex.inr_le_inr_iff.mp h₂) hR
      | exact b.convexQ (Sum.Lex.inr_le_inr_iff.mp h₁) (Sum.Lex.inr_le_inr_iff.mp h₂) hR

def jointLeft : Embedding a (a.jointOrder b) where
  toEmbedding := A.jointLeft B
  lt_iff _ _ := by
    letI := a.order
    letI := b.order
    exact Sum.Lex.inl_lt_inl_iff

def jointRight : Embedding b (a.jointOrder b) where
  toEmbedding := A.jointRight B
  lt_iff _ _ := by
    letI := a.order
    letI := b.order
    exact Sum.Lex.inr_lt_inr_iff

namespace Successor
variable {a b} (s : Successor a) (t : Successor b)

def jointSuccessor : Successor (a.jointOrder b) := by
  letI := a.order
  letI := b.order
  refine {
    next := Sum.map s.next t.next
    sameP := ?_
    le_next := ?_
    least := ?_
    strict := ?_ }
  · rintro (x | x)
    · exact s.sameP x
    · exact t.sameP x
  · rintro (x | x)
    · exact Sum.Lex.inl_le_inl_iff.mpr (s.le_next x)
    · exact Sum.Lex.inr_le_inr_iff.mpr (t.le_next x)
  · rintro (x | x) (y | y) hP hxy
    · exact Sum.Lex.inl_le_inl_iff.mpr (s.least x y hP (Sum.Lex.inl_lt_inl_iff.mp hxy))
    · exact False.elim hP
    · exact False.elim hP
    · exact Sum.Lex.inr_le_inr_iff.mpr (t.least x y hP (Sum.Lex.inr_lt_inr_iff.mp hxy))
  · rintro (x | x) ⟨(y | y), hP, hxy⟩
    · exact Sum.Lex.inl_lt_inl_iff.mpr (s.strict x ⟨y, hP, Sum.Lex.inl_lt_inl_iff.mp hxy⟩)
    · exact False.elim hP
    · exact False.elim hP
    · exact Sum.Lex.inr_lt_inr_iff.mpr (t.strict x ⟨y, hP, Sum.Lex.inr_lt_inr_iff.mp hxy⟩)

def jointLeft : Embedding s (s.jointSuccessor t) where
  toOrderedEmbedding := a.jointLeft b
  map_next _ := rfl

def jointRight : Embedding t (s.jointSuccessor t) where
  toOrderedEmbedding := a.jointRight b
  map_next _ := rfl

end Successor
end ConvexOrder
end Nested
end CCO.ResetOrder.Counterexample
