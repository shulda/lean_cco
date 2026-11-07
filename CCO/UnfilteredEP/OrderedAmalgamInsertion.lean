import CCO.ResetOrder.Hierarchy.Orders

/-! The explicit fibre-shuffle step used by the actual reset amalgam.
One fresh point can be placed immediately after a prescribed old point,
retaining EVERY comparison of the entire old carrier. This lemma asserts
no ordered SAP: its freshness and complete-carrier hypotheses are explicit. -/

universe u v
namespace CCO.UnfilteredEP.OrderedAmalgamInsertion
open ResetOrder.Hierarchy

variable {X : Type u} {Y : Type v}

/-- Insert `none` immediately after `anchor`, with all old comparisons fixed. -/
def insertedRelation (o : TotalOrder X) (anchor : X) : Option X → Option X → Prop
  | none,none => False
  | some x,none => x = anchor ∨ o.lt x anchor
  | none,some y => o.lt anchor y
  | some x,some y => o.lt x y

def insertAfter (o : TotalOrder X) (anchor : X) : TotalOrder (Option X) where
  lt := insertedRelation o anchor
  irrefl x := by
    cases x with
    | none => exact False.elim
    | some x => exact o.irrefl x
  trans := by
    intro x y z hxy hyz
    cases x with
    | none =>
      cases y with
      | none => exact hxy.elim
      | some y =>
        cases z with
        | none =>
          rcases hyz with he | hyu
          · subst y
            exact (o.irrefl anchor hxy).elim
          · exact (o.asymm hxy hyu).elim
        | some z => exact o.trans hxy hyz
    | some x =>
      cases y with
      | none =>
        cases z with
        | none => exact hyz.elim
        | some z =>
          rcases hxy with rfl | hxu
          · exact hyz
          · exact o.trans hxu hyz
      | some y =>
        cases z with
        | none =>
          right
          rcases hyz with rfl | hyu
          · exact hxy
          · exact o.trans hxy hyu
        | some z => exact o.trans hxy hyz
  total := by
    intro x y different
    cases x with
    | none =>
      cases y with
      | none => exact (different rfl).elim
      | some y =>
        by_cases he : y = anchor
        · exact Or.inr (Or.inl he)
        · rcases o.total (Ne.symm he) with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inr h)
    | some x =>
      cases y with
      | none =>
        by_cases he : x = anchor
        · exact Or.inl (Or.inl he)
        · rcases o.total he with h | h
          · exact Or.inl (Or.inr h)
          · exact Or.inr h
      | some y =>
        exact o.total (fun he => different (congrArg some he))

@[simp] theorem insertAfter_old (o : TotalOrder X) (anchor x y : X) :
    (insertAfter o anchor).lt (some x) (some y) ↔ o.lt x y := Iff.rfl

theorem insertAfter_left (o : TotalOrder X) (anchor : X) :
    (insertAfter o anchor).lt (some anchor) none := Or.inl rfl

theorem insertAfter_right (o : TotalOrder X) (anchor y : X) (h : o.lt anchor y) :
    (insertAfter o anchor).lt none (some y) := h

/-- The actual strong-amalgam union when a named sort gains one fresh point. -/
noncomputable def freshCarrierEquiv (f : X ↪ Y) (z : Y)
    (fresh : z ∉ Set.range f) (cover : ∀ y : Y, y = z ∨ ∃ x, f x = y) :
    Option X ≃ Y := by
  let point : Option X → Y := fun p => p.elim z f
  apply Equiv.ofBijective point
  constructor
  · intro x y same
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some y => exact (fresh ⟨y,same.symm⟩).elim
    | some x =>
      cases y with
      | none => exact (fresh ⟨x,same⟩).elim
      | some y => exact congrArg some (f.injective same)
  · intro y
    rcases cover y with rfl | ⟨x,hx⟩
    · exact ⟨none,rfl⟩
    · exact ⟨some x,hx⟩

/-- Concrete insertion in an actual old/fresh carrier. The complete old
order is retained, and the new point is between the prescribed endpoints. -/
theorem extend_one_fresh (o : TotalOrder X) (f : X ↪ Y) (z : Y)
    (fresh : z ∉ Set.range f) (cover : ∀ y : Y, y = z ∨ ∃ x, f x = y)
    (left right : X) (comparison : o.lt left right) :
    ∃ target : TotalOrder Y,
      (∀ x y, target.lt (f x) (f y) ↔ o.lt x y) ∧
      target.lt (f left) z ∧ target.lt z (f right) := by
  let e := freshCarrierEquiv f z fresh cover
  let target := TotalOrder.pullback (insertAfter o left) e.symm e.symm.injective
  have old (x : X) : e.symm (f x) = some x := e.symm_apply_apply (some x)
  have new : e.symm z = none := e.symm_apply_apply none
  refine ⟨target,?_,?_,?_⟩
  · intro x y
    change (insertAfter o left).lt (e.symm (f x)) (e.symm (f y)) ↔ o.lt x y
    rw [old,old]
    exact Iff.rfl
  · change (insertAfter o left).lt (e.symm (f left)) (e.symm z)
    rw [old,new]
    exact insertAfter_left o left
  · change (insertAfter o left).lt (e.symm z) (e.symm (f right))
    rw [old,new]
    exact insertAfter_right o left right comparison

end CCO.UnfilteredEP.OrderedAmalgamInsertion
