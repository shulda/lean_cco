import CCO.UnfilteredEP.SynchronizedPairType
import CCO.UnfilteredEP.HierarchyComparisons

/-! Concrete discharge of the two synchronized-order context laws.
This consumer is deliberately separate from the strict generic complete
orbital proof, whose dependency closure does not use normalization. -/

universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (hC : ActualAge B ht C) (proper : ∀ x, ProperSort B ht (C.sort x))
variable (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V)

/-- The actual constructed hierarchy satisfies exactly the two explicit
order-context assumptions of the independent complete-orbital theorem. -/
theorem hierarchicalPairOrderContext :
    SynchronizedPairOrder B ht C hC priority (hierarchicalOrder B ht C proper hC priority o) where
  path_parent p x y hp := hierarchicalOrder_path_parent B ht C proper hC priority o p x y hp
  different_sort x y hne := hierarchicalOrder_different_sort B ht C proper hC priority o x y hne

/-- A fixed normalized object supplies that same explicit context on its
original total order, preserving its entire carrier and all old symbols. -/
theorem fixedPairOrderContext
    (fixed : hierarchicalOrder B ht C proper hC priority o = o) :
    SynchronizedPairOrder B ht C hC priority o :=
  Eq.mp (congrArg (fun p => SynchronizedPairOrder B ht C hC priority p) fixed)
    (hierarchicalPairOrderContext B ht C hC proper priority o)

end
end CCO.UnfilteredEP
