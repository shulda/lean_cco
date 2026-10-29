import CCO.UnarySupport.Induced

universe u v
namespace CCO.UnarySupport.Structure
variable {L : Signature.{u}} {V : Type v}

/-- Closed factors retain all unary domains and values. Nullary diagrams
agree literally in every restriction, including the empty intersection. -/
structure FreeDecomposition (C : Structure L V) where
  left : Set V
  right : Set V
  left_closed : C.IsClosed left
  right_closed : C.IsClosed right
  cover : left ∪ right = Set.univ
  left_proper : left ≠ Set.univ
  right_proper : right ≠ Set.univ
  rel_local : ∀ R xs, C.rel R xs → (∀ i, xs i ∈ left) ∨ (∀ i, xs i ∈ right)

def Irreducible (C : Structure L V) : Prop := IsEmpty (FreeDecomposition C)

theorem irreducible_of_generated (C : Structure L V) (x : V)
    (hx : C.closure {x} = Set.univ) : C.Irreducible := by
  constructor
  intro d
  have hcover : x ∈ d.left ∨ x ∈ d.right := by rw [← Set.mem_union, d.cover]; trivial
  rcases hcover with hl | hr
  · apply d.left_proper
    apply Set.eq_univ_of_forall
    intro y
    exact C.closure_minimal d.left_closed (by simpa using hl) (hx ▸ Set.mem_univ y)
  · apply d.right_proper
    apply Set.eq_univ_of_forall
    intro y
    exact C.closure_minimal d.right_closed (by simpa using hr) (hx ▸ Set.mem_univ y)

theorem singleton_irreducible (C : Structure L V) (x : V) :
    (C.singletonStructure x).Irreducible :=
  irreducible_of_generated _ ⟨x, C.mem_closureAt x⟩ (C.singleton_generated x)

end CCO.UnarySupport.Structure
