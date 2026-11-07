import CCO.UnfilteredEP.OrderedAmalgamInsertion
import CCO.TerminalHiddenHN.FiniteOrderExtension
import Mathlib.Order.RelClasses

/-! Raw finite sort orders extend on the SAME whole old map, including
empty sorts. The one fresh task is inserted as specified; all other raw
sort orders are extended before the actual hierarchical normalization. -/

universe u v
namespace CCO.UnfilteredEP.OrderedAmalgamInsertion
open ResetOrder.Hierarchy
noncomputable section
variable {X : Type u} {Y : Type v}

@[instance_reducible] def asLinearOrder (o : TotalOrder X) : LinearOrder X := by
  classical
  letI : IsStrictTotalOrder X o.lt := {
    irrefl := o.irrefl
    trans := fun _ _ _ => o.trans
    trichotomous := by
      intro x y notForward notBackward
      by_contra different
      exact (o.total different).elim notForward notBackward }
  exact linearOrderOfSTO o.lt

def ofLinearOrder (o : LinearOrder X) : TotalOrder X := by
  letI := o
  exact ⟨(· < ·),lt_irrefl,fun h h' => lt_trans h h',fun h => lt_or_gt_of_ne h⟩

/-- Every complete raw old order extends on its supplied injection. -/
theorem extend_finite [Finite Y] (o : TotalOrder X) (f : X → Y)
    (injective : Function.Injective f) :
    ∃ target : TotalOrder Y, ∀ x y, target.lt (f x) (f y) ↔ o.lt x y := by
  letI := asLinearOrder o
  obtain ⟨target,extensionLaw⟩ := CCO.TerminalHiddenHN.finite_linearOrder_extension f injective
  exact ⟨ofLinearOrder target,extensionLaw⟩

/-- The only extra comparison is the single fresh midpoint in its
specified task; every other old comparison is preserved AND reflected. -/
theorem insert_finite_midpoint [Finite Y] (o : TotalOrder X)
    (f : X ↪ Y) (z : Y) (fresh : z ∉ Set.range f)
    (onlyNew : ∀ x y : Y, x ∉ Set.range f → y ∉ Set.range f → x = y)
    (left right : X) (comparison : o.lt left right) :
    ∃ target : TotalOrder Y,
      (∀ x y, target.lt (f x) (f y) ↔ o.lt x y) ∧
      target.lt (f left) z ∧ target.lt z (f right) := by
  classical
  apply extend_one_fresh o f z fresh _ left right comparison
  intro y
  by_cases old : y ∈ Set.range f
  · exact Or.inr old
  · exact Or.inl (onlyNew y z old fresh)

end
end CCO.UnfilteredEP.OrderedAmalgamInsertion
