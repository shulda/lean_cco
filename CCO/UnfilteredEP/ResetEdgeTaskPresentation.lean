import CCO.UnfilteredEP.NormalizedTaskProvider

/-! Exact raw presentation of the full normalized task provider. The
canonical decoded old functions and the normalized witness have the
same entire structure, carrier and literal reset cylinders. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)
variable (D : HiddenCut B) (m : ActualResetMenu B (fullMIOfNamed B D.1 D.2))
variable (priority : LinearOrder (Sig B ht).Sorts)
variable {A : ResetOrder.Unary.FullObject (actualTaskFibres B ht n D m) (normalizedTaskExtra B ht n)}
variable (hA : normalizedTaskFullAge B ht n D m priority A)

/-- Forgetting the global order is literally the retained old base. -/
theorem normalizedTaskDecode_base :
    (normalizedTaskDecode B ht n D m A).reduct (coordinateOrderExpansion B ht).toReduct =
      taskOldBase B ht n A.task.old := by
  apply Structure.ext_data
    (C := (normalizedTaskDecode B ht n D m A).reduct (coordinateOrderExpansion B ht).toReduct)
    (D := taskOldBase B ht n A.task.old) rfl rfl
  · funext U
    exact PEmpty.elim U
  · funext R x y
    rfl

theorem normalizedTaskBase_presentation :
    taskOldBase B ht n A.task.old = CoordinateModel B ht
      (normalizedPresentation B ht priority hA.normalized).raw := by
  let Q := normalizedPresentation B ht priority hA.normalized
  have he : normalizedTaskDecode B ht n D m A =
      @OrderedCoordinateModel B ht A.task.old.Carrier Q.raw Q.order := Q.model_eq
  refine (normalizedTaskDecode_base B ht n D m).symm.trans
    ((congrArg (fun C => C.reduct (coordinateOrderExpansion B ht).toReduct) he).trans ?_)
  apply Structure.ext_data
    (C := (@OrderedCoordinateModel B ht A.task.old.Carrier Q.raw Q.order).reduct
      (coordinateOrderExpansion B ht).toReduct)
    (D := CoordinateModel B ht Q.raw) rfl rfl
  · funext U
    exact PEmpty.elim U
  · funext R x y
    rfl

/-- All actual old functions, their domains and fine cylinders agree;
this is equality of structures, rather than an abstract old-map premise. -/
theorem normalizedTaskRaw_presentation :
    taskOldRaw B ht n A.task.old = (normalizedPresentation B ht priority hA.normalized).raw := by
  unfold taskOldRaw
  rw [normalizedTaskBase_presentation B ht n D m priority hA]
  exact TerminalHiddenHN.binaryDecode_binaryStructure _ _ _

/-- The current task comparison is one of the full global comparisons. -/
theorem normalizedTask_comparison_global (x y : A.task.old.Carrier)
    (h : A.task.order.lt x y) :
    @LT.lt _ (normalizedPresentation B ht priority hA.normalized).order.toLT x y := by
  have h' := (hA.comparison x y).mp h
  have hg := h'.2
  let Q := normalizedPresentation B ht priority hA.normalized
  have he : normalizedTaskDecode B ht n D m A =
      @OrderedCoordinateModel B ht A.task.old.Carrier Q.raw Q.order := Q.model_eq
  rw [he] at hg
  exact hg.2.2

/-- The retained actual complete cylinder is read in the SAME raw
normalized presentation used by every source comparison theorem. -/
theorem normalizedTask_reset_presentation (x y : A.task.old.Carrier)
    (h : (actualTaskFibres B ht n D m).reset A.task.old x y) :
    (actualCutFormula B ht D m).reset
      (CoordinateModel B ht (normalizedPresentation B ht priority hA.normalized).raw) x y := by
  change (actualCutFormula B ht D m).reset (taskOldBase B ht n A.task.old) x y at h
  rw [normalizedTaskBase_presentation B ht n D m priority hA] at h
  exact h

end
end CCO.UnfilteredEP
