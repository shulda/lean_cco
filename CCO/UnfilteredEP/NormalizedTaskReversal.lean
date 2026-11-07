import CCO.UnfilteredEP.NormalizedTaskProvider
import CCO.UnfilteredEP.TaskReversalModel

/-! Relative reversal for the literal full-provider image of one task.
All earlier task relations remain exactly the same old structure. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (i : Fin (taskCount B ht))
variable (m : ActualResetMenu B (fullMIOfNamed B (taskCut B ht i).1 (taskCut B ht i).2))
variable (priority : LinearOrder (Sig B ht).Sorts)
local notation "P" => actualTaskFibres B ht i.val (taskCut B ht i) m
local notation "X" => normalizedTaskExtra B ht i.val
local notation "R" => normalizedTaskFullAge B ht i.val (taskCut B ht i) m priority
def normalizedTaskReverseFull
    (F : ResetOrder.Unary.FullObject (P) (X)) (hF : R F) :
    ResetOrder.Unary.FullObject (P) (X) where
  task := ResetOrder.Unary.reverse F.task
  func := PEmpty.elim
  functional f := PEmpty.elim f
  func_sorted f := PEmpty.elim f
  rel p xs := (reverseTaskModel B ht priority hF.normalized i).binary (.inr p) (xs 0) (xs 1)
  rel_sorted p xs h k := by
    change (reverseTaskModel B ht priority hF.normalized i).binary (.inr p) (xs 0) (xs 1) at h
    have hs := (reverseTaskModel B ht priority hF.normalized i).binary_sorted (.inr p) (xs 0) (xs 1) h
    have he : (reverseTaskModel B ht priority hF.normalized i).sort = F.task.old.data.sort :=
      congrArg (fun C : Structure (CoordinateLanguage B ht) F.task.old.Carrier => C.sort)
        (reverseTaskModel_base B ht priority hF.normalized i)
    fin_cases k
    · exact (congrFun he (xs 0)).symm.trans hs.1
    · exact (congrFun he (xs 1)).symm.trans hs.2

theorem normalizedTaskReverseFull_decode
    (F : ResetOrder.Unary.FullObject (P) (X)) (hF : R F) :
    normalizedTaskDecode B ht i.val (taskCut B ht i) m
      (normalizedTaskReverseFull B ht i m priority F hF) =
      reverseTaskModel B ht priority hF.normalized i := by
  have hb := reverseTaskModel_base B ht priority hF.normalized i
  apply Structure.ext_data
    (C := normalizedTaskDecode B ht i.val (taskCut B ht i) m
      (normalizedTaskReverseFull B ht i m priority F hF))
    (D := reverseTaskModel B ht priority hF.normalized i)
  · exact (congrArg (fun C : Structure (CoordinateLanguage B ht) F.task.old.Carrier => C.sort) hb).symm
  · exact (congrArg (fun C : Structure (CoordinateLanguage B ht) F.task.old.Carrier => C.func) hb).symm
  · funext U
    exact PEmpty.elim U
  · funext S x y
    cases S with
    | inl S => exact congrFun (congrFun (congrFun
        (congrArg (fun C : Structure (CoordinateLanguage B ht) F.task.old.Carrier => C.binary) hb).symm S) x) y
    | inr p => rfl

theorem normalizedTaskReverseFull_mem
    (F : ResetOrder.Unary.FullObject (P) (X)) (hF : R F) : R (normalizedTaskReverseFull B ht i m priority F hF) := by
  have hd := normalizedTaskReverseFull_decode B ht i m priority F hF
  constructor
  · change NormalizedProperAge B ht priority ⟨F.task.old.Carrier,_,F.task.old.finite⟩
    rw [hd]
    exact reverseTaskModel_mem B ht priority hF.normalized i
  · change resetUnaryDecode (PrefixFullCodeLanguage B ht i.val) F.task.old.data = _
    rw [hd]
    exact hF.prefix_eq.trans (reverseTaskModel_prefix B ht priority hF.normalized i).symm
  · intro x y
    change F.task.order.lt y x ↔ _
    rw [hd,hF.comparison y x]
    constructor
    · rintro ⟨hp,ho⟩
      have hp' := (actualParentFormula B ht (taskCut B ht i)).same_symm _ hp
      refine ⟨hp',?_⟩
      exact (reverseTaskModel_comparison B ht priority hF.normalized i x y hp').mpr ho
    · rintro ⟨hp,ho⟩
      refine ⟨(actualParentFormula B ht (taskCut B ht i)).same_symm _ hp,?_⟩
      exact (reverseTaskModel_comparison B ht priority hF.normalized i x y hp).mp ho

/-- C68/I12 reversal uses an actual legal full expansion of the same
old prefix; the upper task comparison is reversed point for point. -/
theorem normalizedTaskUpperAge_reverse
    (A : ResetOrder.Unary.TaskObject (P))
    (hA : normalizedTaskUpperAge B ht i.val (taskCut B ht i) m priority A) :
    normalizedTaskUpperAge B ht i.val (taskCut B ht i) m priority
      (ResetOrder.Unary.reverse A) := by
  obtain ⟨F,hF,he⟩ := hA
  refine ⟨normalizedTaskReverseFull B ht i m priority F hF,
    normalizedTaskReverseFull_mem B ht i m priority F hF,?_⟩
  exact congrArg ResetOrder.Unary.reverse he

end
end CCO.UnfilteredEP
