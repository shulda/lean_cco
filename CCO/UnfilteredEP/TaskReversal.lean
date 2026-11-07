import CCO.UnfilteredEP.ActualTaskFibres
import CCO.UnfilteredEP.HierarchyReversal
import CCO.UnfilteredEP.HierarchyFixedMaps

/-! Actual one-task reversal fixes the entire exposed prefix, on the
same carrier and with exactly the same old functions and fine relations. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)
variable {V : Type z} (C : UnarySupport.Structure (Sig B ht) V)
variable (proper : ∀x, ProperSort B ht (C.sort x)) (hC : ActualAge B ht C)
variable (o : LinearOrder V)
variable (fixed : hierarchicalOrder B ht C proper hC priority o = o)

include fixed

theorem reversed_task_other_comparison (i j : Fin (taskCount B ht)) (hne : j ≠ i)
    (x y : V) (hparent : (actualParentFormula B ht (taskCut B ht j)).same
      (CoordinateModel B ht C) x y) :
    @LT.lt _ (reverseHierarchicalOrder B ht C proper hC priority o
      (taskEnumeration B ht i)).toLT x y ↔ @LT.lt _ o.toLT x y := by
  let xd : HiddenCutCarrier B ht C (taskCut B ht j) := ⟨x,hparent.1⟩
  let yd : HiddenCutCarrier B ht C (taskCut B ht j) := ⟨y,hparent.2.1⟩
  have hp := (actualParentFormula_same_iff B ht C hC (taskCut B ht j) xd yd).mp hparent
  have hr := reverseHierarchicalOrder_other_parent B ht C proper hC priority o
    (taskEnumeration B ht i) (taskEnumeration B ht j)
    (fun he => hne ((taskEnumeration B ht).injective he))
    (cutRepresentative B ht (taskEnumeration B ht j)) xd yd hp
  rw [fixed] at hr
  exact hr

theorem reversed_task_selected_comparison (i : Fin (taskCount B ht))
    (x y : V) (hparent : (actualParentFormula B ht (taskCut B ht i)).same
      (CoordinateModel B ht C) x y) :
    @LT.lt _ (reverseHierarchicalOrder B ht C proper hC priority o
      (taskEnumeration B ht i)).toLT x y ↔ @LT.lt _ o.toLT y x := by
  let xd : HiddenCutCarrier B ht C (taskCut B ht i) := ⟨x,hparent.1⟩
  let yd : HiddenCutCarrier B ht C (taskCut B ht i) := ⟨y,hparent.2.1⟩
  have hp := (actualParentFormula_same_iff B ht C hC (taskCut B ht i) xd yd).mp hparent
  have hr := reverseHierarchicalOrder_selected B ht C proper hC priority o
    (taskEnumeration B ht i) (cutRepresentative B ht (taskEnumeration B ht i)) xd yd hp
  rw [fixed] at hr
  exact hr

/-- C49 at the concrete C69 language: reversing task i retains EVERY
relation of prefix i, rather than only its proper unary reduct. -/
theorem taskPrefixData_reverse (i : Fin (taskCount B ht)) :
    taskPrefixData B ht i.val
      (@OrderedCoordinateModel B ht V C
        (reverseHierarchicalOrder B ht C proper hC priority o (taskEnumeration B ht i))) =
      taskPrefixData B ht i.val (@OrderedCoordinateModel B ht V C o) := by
  apply Structure.ext_data
    (C := taskPrefixData B ht i.val
      (@OrderedCoordinateModel B ht V C
        (reverseHierarchicalOrder B ht C proper hC priority o (taskEnumeration B ht i))))
    (D := taskPrefixData B ht i.val (@OrderedCoordinateModel B ht V C o)) rfl rfl rfl
  funext R x y
  cases R with
  | inl R => rfl
  | inr j =>
    apply propext
    change (_ ∧ (C.sort x = _ ∧ C.sort y = _ ∧ _)) ↔
      (_ ∧ (C.sort x = _ ∧ C.sort y = _ ∧ _))
    apply and_congr_right
    intro hp
    apply and_congr_right
    intro _
    apply and_congr_right
    intro _
    exact reversed_task_other_comparison B ht priority C proper hC o fixed i j.val
      (fun he => (Nat.ne_of_lt j.property) (congrArg Fin.val he)) x y hp

end
end CCO.UnfilteredEP
