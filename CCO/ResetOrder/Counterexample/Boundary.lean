import CCO.ResetOrder.Counterexample.Failure

/-! The upper expansion is not reasonable: inserting a middle point changes
the uniquely determined successor. This is a boundary of the displayed EP
quantifiers, not a counterexample to an additional reasonableness hypothesis. -/
namespace CCO.ResetOrder.Counterexample

def endpoints : Set (Fin 3) := {x | x = 0 ∨ x = 2}

def endpointOrder := patternOrder.induce endpoints

def leftEndpoint : endpoints := ⟨0, Or.inl rfl⟩
def rightEndpoint : endpoints := ⟨2, Or.inr rfl⟩

def endpointSuccessor : endpointOrder.Successor where
  next _ := rightEndpoint
  sameP _ := rfl
  le_next x := by
    change x.val ≤ (2 : Fin 3)
    exact Fin.le_last x.val
  least x y _ hxy := by
    change (2 : Fin 3) ≤ y.val
    rcases y.property with hy | hy
    · change x.val < y.val at hxy
      rw [hy] at hxy
      exact False.elim ((not_lt_of_ge (Fin.zero_le _)) hxy)
    · rw [hy]
  strict x h := by
    obtain ⟨y, _, hxy⟩ := h
    change x.val < (2 : Fin 3)
    exact lt_of_lt_of_le hxy (Fin.le_last y.val)

/-- The induced inclusion preserves P,Q and order, but no allowed choice of
target successor lifts that very same vertex map. -/
theorem upper_not_reasonable :
    ∀ t : patternOrder.Successor,
      ¬ ∃ e : Nested.ConvexOrder.Successor.Embedding endpointSuccessor t,
        ∀ x, e.point x = x.val := by
  intro t
  have ht := t.unique patternSuccessor
  subst t
  rintro ⟨e, he⟩
  have h := e.map_next leftEndpoint
  change e.point rightEndpoint = patternNext (e.point leftEndpoint) at h
  rw [he, he] at h
  change (2 : Fin 3) = 1 at h
  exact (show (2 : Fin 3) ≠ 1 by decide) h

/-- There really is an old induced embedding whose lift fails. -/
def oldEndpointInclusion : Nested.ConvexOrder.Embedding endpointOrder patternOrder :=
  patternOrder.inclusion endpoints

end CCO.ResetOrder.Counterexample
