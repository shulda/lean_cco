import CCO.UnfilteredEP.ActualTaskEP

/-! C69--C71: the actual finite chain of I12 tasks composes through the
accepted I14 unchanged-function theorem to the full normalized hidden EP. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- Source-instance hidden EP on the whole proper hidden age. Every
function and every allowed exact-carrier normalized expansion is retained;
no Ramsey, midpoint, reset-type or intermediate-EP provider remains. -/
theorem actual_normalized_hidden_EP (priority : LinearOrder (Sig B ht).Sorts) :
    (actualNormalizedExpansionAges B ht priority).HiddenEP :=
  actual_normalized_hidden_EP_of_unary_tasks B ht priority (actual_task_EP B ht priority)

end
end CCO.UnfilteredEP
