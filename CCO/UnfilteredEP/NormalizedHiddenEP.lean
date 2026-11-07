import CCO.UnfilteredEP.TaskTowerReceiving
import CCO.UnfilteredEP.NormalizedExpansionAges

/-! The exact normalized ExpansionAges consumer of finite I12 tasks. -/
universe u v w
namespace CCO.UnfilteredEP
open CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)

/-- Every arbitrary normalized expansion of the chosen entire old host
receives the source. The source-age hypotheses are exactly those of the
concrete normalized expansion package. -/
theorem actual_normalized_hidden_EP_of_taskSteps
    (singleTask : ∀ i, i < taskCount B ht →
      CCO.ResetOrder.Generic.RelativeEP (taskTowerStep B ht i)
        (taskTowerClass.{u,v,w,max u v} B ht priority (i+1)) (taskTowerClass B ht priority i)) :
    (actualNormalizedExpansionAges B ht priority).HiddenEP := by
  intro A _ a
  obtain ⟨H,hH,witness⟩ := normalized_order_witness_of_taskSteps B ht priority singleTask
    a.toHidden a.member
  exact ⟨H.reduct (coordinateOrderExpansion B ht).toReduct,
    normalized_reduct_member B ht priority H hH,witness⟩

end
end CCO.UnfilteredEP
