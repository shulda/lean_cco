import CCO.ResetOrder.Hierarchy.Orders

/-! A fixed priority on sort symbols combines the actual normalized sort
orders into one genuine total order, with unchanged sort-preserving maps. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy

def SortLex {I : Type u} {X : I → Type v} (priority : TotalOrder I)
    (orders : ∀ i, TotalOrder (X i)) (x y : Sigma X) : Prop :=
  priority.lt x.1 y.1 ∨ ∃ h : x.1 = y.1, (orders y.1).lt (h ▸ x.2) y.2

def sortOrder {I : Type u} {X : I → Type v} (priority : TotalOrder I)
    (orders : ∀ i, TotalOrder (X i)) : TotalOrder (Sigma X) where
  lt := SortLex priority orders
  irrefl := by
    rintro ⟨i,x⟩ (hi | ⟨he,hx⟩)
    · exact priority.irrefl i hi
    · exact (orders i).irrefl x hx
  trans := by
    rintro ⟨i,x⟩ ⟨j,y⟩ ⟨k,z⟩ h h'
    rcases h with hi | ⟨he,hx⟩ <;> rcases h' with hj | ⟨he',hy⟩
    · exact Or.inl (priority.trans hi hj)
    · cases he'; exact Or.inl hi
    · cases he; exact Or.inl hj
    · cases he; cases he'; exact Or.inr ⟨rfl,(orders i).trans hx hy⟩
  total := by
    rintro ⟨i,x⟩ ⟨j,y⟩ hne
    by_cases he : i = j
    · subst j
      have hxy : x ≠ y := fun h => hne (by cases h; rfl)
      exact ((orders i).total hxy).imp (fun h => Or.inr ⟨rfl,h⟩) (fun h => Or.inr ⟨rfl,h⟩)
    · exact (priority.total he).imp Or.inl Or.inl

theorem sortOrder_same {I : Type u} {X : I → Type v} (priority : TotalOrder I)
    (orders : ∀ i, TotalOrder (X i)) (i : I) (x y : X i) :
    (sortOrder priority orders).lt ⟨i,x⟩ ⟨i,y⟩ ↔ (orders i).lt x y := by
  constructor
  · rintro (h | ⟨_,h⟩)
    · exact False.elim (priority.irrefl i h)
    · exact h
  · exact fun h => Or.inr ⟨rfl,h⟩

theorem sortOrder_map {I : Type u} {X : I → Type v} {Y : I → Type w}
    (priority : TotalOrder I) (a : ∀ i, TotalOrder (X i)) (b : ∀ i, TotalOrder (Y i))
    (f : ∀ i, X i → Y i)
    (hf : ∀ i x y, (a i).lt x y → (b i).lt (f i x) (f i y))
    (x y : Sigma X) (h : (sortOrder priority a).lt x y) :
    (sortOrder priority b).lt ⟨x.1,f x.1 x.2⟩ ⟨y.1,f y.1 y.2⟩ := by
  obtain ⟨i,x⟩ := x
  obtain ⟨j,y⟩ := y
  rcases h with hi | ⟨he,hx⟩
  · exact Or.inl hi
  · cases he
    exact Or.inr ⟨rfl,hf i x y hx⟩

end CCO.ResetOrder.Hierarchy
