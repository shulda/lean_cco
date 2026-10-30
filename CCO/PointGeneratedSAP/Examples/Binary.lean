import Mathlib.Data.Set.Insert

/-! A genuine mixed-input value: individual singleton closures are closed,
but their union creates a new vertex under a binary operation. -/
namespace CCO.PointGeneratedSAP.Examples.Binary

abbrev Point := Fin 3

def operation (x y : Point) : Point := if x = 0 ∧ y = 1 then 2 else x

inductive Generated (D : Set Point) : Point → Prop
  | base {x} : x ∈ D → Generated D x
  | combine {x y} : Generated D x → Generated D y → Generated D (operation x y)

def closure (D : Set Point) : Set Point := {x | Generated D x}
def Closed (D : Set Point) : Prop := ∀ x ∈ D, ∀ y ∈ D, operation x y ∈ D

theorem subset_closure (D : Set Point) : D ⊆ closure D := fun _ => Generated.base

theorem closure_minimal {D E : Set Point} (hE : Closed E) (hDE : D ⊆ E) :
    closure D ⊆ E := by
  intro x hx
  induction hx with
  | base h => exact hDE h
  | combine _ _ hx hy => exact hE _ hx _ hy

theorem singleton_zero_closed : Closed ({0} : Set Point) := by
  rintro x rfl y rfl
  simp [operation,Set.mem_singleton_iff]

theorem singleton_one_closed : Closed ({1} : Set Point) := by
  rintro x rfl y rfl
  simp [operation,Set.mem_singleton_iff]

theorem closure_zero : closure ({0} : Set Point) = {0} :=
  Set.Subset.antisymm (closure_minimal singleton_zero_closed (Set.Subset.refl _)) (subset_closure _)

theorem closure_one : closure ({1} : Set Point) = {1} :=
  Set.Subset.antisymm (closure_minimal singleton_one_closed (Set.Subset.refl _)) (subset_closure _)

theorem mixed_value : (2 : Point) ∈ closure (({0} : Set Point) ∪ {1}) := by
  have h := Generated.combine (Generated.base (D := ({0} : Set Point) ∪ {1}) (Or.inl rfl))
    (Generated.base (D := ({0} : Set Point) ∪ {1}) (Or.inr rfl))
  simpa [operation,closure] using h

theorem unary_union_equality_fails :
    closure (({0} : Set Point) ∪ {1}) ≠ closure {0} ∪ closure {1} := by
  intro he
  have hm := mixed_value
  rw [he,closure_zero,closure_one] at hm
  simp [Set.mem_singleton_iff] at hm

end CCO.PointGeneratedSAP.Examples.Binary
