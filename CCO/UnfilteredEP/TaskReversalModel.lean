import CCO.UnfilteredEP.TaskReversal

/-! Same-carrier relative reversal for an arbitrary presentation in the
actual normalized full class. These equalities retain the entire old prefix. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)
variable {A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)}
variable (hA : NormalizedProperAge B ht priority A) (i : Fin (taskCount B ht))

def reverseTaskModel : Structure (OrderedCoordinateLanguage B ht) A.Carrier :=
  let Q := normalizedPresentation B ht priority hA
  @OrderedCoordinateModel B ht A.Carrier Q.raw
    (reverseHierarchicalOrder B ht Q.raw Q.proper Q.actual priority Q.order
      (taskEnumeration B ht i))

theorem reverseTaskModel_mem :
    NormalizedProperAge B ht priority ⟨A.Carrier,reverseTaskModel B ht priority hA i,A.finite⟩ := by
  let Q := normalizedPresentation B ht priority hA
  letI : Finite A.Carrier := A.finite
  exact reverseHierarchicalOrder_mem B ht Q.raw Q.proper Q.actual priority Q.order
    (taskEnumeration B ht i)

theorem reverseTaskModel_base :
    (reverseTaskModel B ht priority hA i).reduct (coordinateOrderExpansion B ht).toReduct =
      A.model.reduct (coordinateOrderExpansion B ht).toReduct := by
  rw [(normalizedPresentation B ht priority hA).model_eq]
  rfl

theorem reverseTaskModel_prefix :
    taskPrefixData B ht i.val (reverseTaskModel B ht priority hA i) =
      taskPrefixData B ht i.val A.model := by
  let Q := normalizedPresentation B ht priority hA
  rw [Q.model_eq]
  exact taskPrefixData_reverse B ht priority Q.raw Q.proper Q.actual Q.order Q.fixed i

theorem reverseTaskModel_comparison (x y : A.Carrier)
    (hp : (actualParentFormula B ht (taskCut B ht i)).same
      (A.model.reduct (coordinateOrderExpansion B ht).toReduct) x y) :
    (reverseTaskModel B ht priority hA i).binary
      (.inr (hiddenCutSort B ht (taskCut B ht i),hiddenCutSort B ht (taskCut B ht i))) x y ↔
      A.model.binary
        (.inr (hiddenCutSort B ht (taskCut B ht i),hiddenCutSort B ht (taskCut B ht i))) y x := by
  let Q := normalizedPresentation B ht priority hA
  rw [Q.model_eq] at hp ⊢
  change (Q.raw.sort x = _ ∧ Q.raw.sort y = _ ∧ _) ↔
    (Q.raw.sort y = _ ∧ Q.raw.sort x = _ ∧ _)
  have he := reversed_task_selected_comparison B ht priority Q.raw Q.proper Q.actual
    Q.order Q.fixed i x y hp
  exact ⟨fun h => ⟨h.2.1,h.1,he.mp h.2.2⟩,
    fun h => ⟨h.2.1,h.1,he.mpr h.2.2⟩⟩

end
end CCO.UnfilteredEP
