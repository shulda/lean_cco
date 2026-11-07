import CCO.UnfilteredEP.OrderedAmalgamFiniteOrder

/-! A new point is inserted between the prescribed old endpoints while
EVERY comparison on the whole old base is retained; all remaining points
of the finite host are ordered by actual finite order extension. -/

universe u v
namespace CCO.UnfilteredEP.OrderedAmalgamInsertion
open ResetOrder.Hierarchy
noncomputable section
variable {X : Type u} {Y : Type v}

/-- The entire old base order, not merely the distinguished pair,
extends with the demanded new midpoint in the SAME finite host. -/
theorem finite_insert_over_whole_base [Finite Y] (o : LinearOrder X)
    (f : X ↪ Y) (z : Y) (fresh : z ∉ Set.range f)
    (left right : X) (comparison : @LT.lt _ o.toLT left right) :
    ∃ target : LinearOrder Y,
      (∀ x y, @LT.lt _ target.toLT (f x) (f y) ↔ @LT.lt _ o.toLT x y) ∧
      @LT.lt _ target.toLT (f left) z ∧ @LT.lt _ target.toLT z (f right) := by
  let support : Set Y := Set.range f ∪ {z}
  let old : X ↪ support := {
    toFun x := ⟨f x,Or.inl ⟨x,rfl⟩⟩
    inj' := fun _ _ he => f.injective (congrArg Subtype.val he) }
  let new : support := ⟨z,Or.inr rfl⟩
  have fresh' : new ∉ Set.range old := by
    rintro ⟨x,he⟩
    exact fresh ⟨x,congrArg Subtype.val he⟩
  have cover : ∀ y : support, y = new ∨ ∃ x, old x = y := by
    intro y
    rcases y.property with ⟨x,hx⟩ | hz
    · exact Or.inr ⟨x,Subtype.ext hx⟩
    · exact Or.inl (Subtype.ext hz)
  obtain ⟨order,keeps,before,after⟩ := extend_one_fresh (ofLinearOrder o)
    old new fresh' cover left right comparison
  letI : LinearOrder support := asLinearOrder order
  obtain ⟨target,extensionLaw⟩ := CCO.TerminalHiddenHN.finite_linearOrder_extension
    (A := support) (B := Y) (oldOrder := asLinearOrder order)
    (@Subtype.val Y support) Subtype.val_injective
  refine ⟨target,?_,?_,?_⟩
  · intro x y
    exact (extensionLaw (old x) (old y)).trans (keeps x y)
  · exact (extensionLaw (old left) new).mpr before
  · exact (extensionLaw new (old right)).mpr after

end
end CCO.UnfilteredEP.OrderedAmalgamInsertion
