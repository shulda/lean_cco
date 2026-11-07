import CCO.APRamseyReadout.SortBlockOrder
import CCO.FullCode.Boundaries

/-! Scoped finite diagnostics. These distinguish diagonal comparisons,
unordered shared coordinates, and the HIDDEN-target criterion. They do
not assert EP, EPPA or equality-symbol minimality in an all-order code. -/

namespace CCO.APRamseyReadout.OrderCodeBoundary
noncomputable section

abbrev ascending : LinearOrder (Fin 2) := inferInstance
abbrev descending : LinearOrder (Fin 2) := inferInstanceAs (LinearOrder (OrderDual (Fin 2)))
abbrev priority : LinearOrder Unit := inferInstance
abbrev hiddenSort (_ : Fin 2) : Unit := ()

def singleRootCode (o : LinearOrder (Fin 2)) (_ _ : Unit) : Prop := @LT.lt _ o.toLT 0 1

/-- One literal root has two distinct coordinate-term values. Every
comparison restricted to distinct visible roots misses this difference. -/
theorem diagonal_order_needed :
    (∀ x y : Unit, x ≠ y →
      (singleRootCode ascending x y ↔ singleRootCode descending x y)) ∧
      ¬ (singleRootCode ascending () () ↔ singleRootCode descending () ()) := by
  constructor
  · intro x y h
    exact False.elim (h (Subsingleton.elim _ _))
  · intro h
    have h0 : singleRootCode ascending () () := by change (0 : Fin 2) < 1; decide
    have h1 : ¬ singleRootCode descending () () := by change ¬ (1 : Fin 2) < 0; decide
    exact h1 (h.mp h0)

abbrev visibleTag := Bool
abbrev termValue (tag : visibleTag) : Fin 2 := if tag then 1 else 0

/-- Distinct visible tags have terms in ONE hidden target sort. Both
orders remain legal block orders, and their cross-visible code reverses. -/
theorem different_visible_same_target :
    (false : visibleTag) ≠ true ∧ hiddenSort (termValue false) = hiddenSort (termValue true) ∧
      @LT.lt _ (sortBlockOrder hiddenSort priority ascending).toLT (termValue false) (termValue true) ∧
      ¬ @LT.lt _ (sortBlockOrder hiddenSort priority descending).toLT (termValue false) (termValue true) := by
  refine ⟨by decide,rfl,?_,?_⟩
  · exact (sortBlockOrder_same hiddenSort priority ascending
      (x := termValue false) (y := termValue true) rfl).mpr (by change (0 : Fin 2) < 1; decide)
  · intro h
    have h1 : ¬ @LT.lt _ descending.toLT (termValue false) (termValue true) := by
      change ¬ (1 : Fin 2) < 0
      decide
    exact h1 ((sortBlockOrder_same hiddenSort priority descending
      (x := termValue false) (y := termValue true) rfl).mp h)

/-- The accepted concrete full-code equality example is UNORDERED.
It makes no independence assertion about the actual all-order language. -/
theorem unordered_shared_coordinate_code :
    CCO.FullCode.EqualityCode CCO.FullCode.Boundaries.twoForms
      CCO.FullCode.Boundaries.sharedLeft CCO.FullCode.Boundaries.sharedRight
      (CCO.FullCode.Boundaries.identityPresentation 2 1)
      (CCO.FullCode.Boundaries.identityPresentation 2 0) ∧
    ¬ CCO.FullCode.EqualityCode CCO.FullCode.Boundaries.twoForms
      CCO.FullCode.Boundaries.disjointLeft CCO.FullCode.Boundaries.disjointRight
      (CCO.FullCode.Boundaries.identityPresentation 2 1)
      (CCO.FullCode.Boundaries.identityPresentation 2 0) :=
  CCO.FullCode.Boundaries.cross_root_equality_essential

/-- Sending the shared source coordinate along two unrelated root maps
cannot be extended to even one hidden vertex function. -/
theorem no_shared_coordinate_extension :
    ¬ ∃ f : Fin 3 → Fin 4, f 0 = 0 ∧ f 1 = 1 ∧ f 1 = 2 ∧ f 2 = 3 := by
  rintro ⟨f,_,h1,h2,_⟩
  exact (by decide : (1 : Fin 4) ≠ 2) (h1.symm.trans h2)

/-- In the stronger ALL-order language, the two strict comparison
directions already define equality; no contrary minimality is claimed. -/
theorem all_order_equality_definition {V : Type*} [LinearOrder V] (x y : V) :
    x = y ↔ ¬ x < y ∧ ¬ y < x := by
  constructor
  · rintro rfl
    exact ⟨lt_irrefl _,lt_irrefl _⟩
  · rintro ⟨hxy,hyx⟩
    exact le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)

end
end CCO.APRamseyReadout.OrderCodeBoundary
