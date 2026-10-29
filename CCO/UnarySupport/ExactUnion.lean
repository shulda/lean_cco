import CCO.UnarySupport.Irreducible

universe u v
namespace CCO.UnarySupport.Structure.FreeDecomposition
variable {L : Signature.{u}} {V : Type v} {C : Structure L V}

theorem intersection_closed (d : C.FreeDecomposition) : C.IsClosed (d.left ∩ d.right) :=
  C.isClosed_inter d.left_closed d.right_closed

/-- Every already-defined function graph edge is present in an entire
factor. This includes domain retention, not just a truncated graph union. -/
theorem function_union (d : C.FreeDecomposition) (F : L.Func) (x y : V) :
    y ∈ C.func F x ↔
      (y ∈ C.func F x ∧ x ∈ d.left ∧ y ∈ d.left) ∨
      (y ∈ C.func F x ∧ x ∈ d.right ∧ y ∈ d.right) := by
  constructor
  · intro h
    have hx : x ∈ d.left ∨ x ∈ d.right := by rw [← Set.mem_union, d.cover]; trivial
    rcases hx with hl | hr
    · exact Or.inl ⟨h, hl, d.left_closed F x hl h⟩
    · exact Or.inr ⟨h, hr, d.right_closed F x hr h⟩
  · rintro (⟨h, _, _⟩ | ⟨h, _, _⟩) <;> exact h

/-- The full induced relational union is exact for EVERY symbol and arity,
including nullaries and repeated coordinates. -/
theorem relation_union (d : C.FreeDecomposition) (R : L.Rel)
    (xs : Fin (L.arity R) → V) :
    C.rel R xs ↔
      (C.rel R xs ∧ ∀ i, xs i ∈ d.left) ∨
      (C.rel R xs ∧ ∀ i, xs i ∈ d.right) := by
  constructor
  · intro h
    rcases d.rel_local R xs h with hl | hr
    · exact Or.inl ⟨h, hl⟩
    · exact Or.inr ⟨h, hr⟩
  · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h

end CCO.UnarySupport.Structure.FreeDecomposition
