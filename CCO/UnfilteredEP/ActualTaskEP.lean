import CCO.UnfilteredEP.ActualResetSetting
import CCO.UnfilteredEP.NormalizedTaskMidpoint
import CCO.UnfilteredEP.ResetEdgeTaskTemplate
import CCO.UnfilteredEP.NormalizedTaskComposition

/-! C68/I12 applied to every actual representative task. All providers
are the same normalized hidden class, with complete generated reset
edge types and midpoint extensions over the entire inherited base. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- The genuine relative one-task EP, with one old host fixed before
every exact-carrier competitor, and with all earlier tasks retained. -/
theorem actual_task_EP (priority : LinearOrder (Sig B ht).Sorts)
    (i : Fin (taskCount B ht)) :
    ResetOrder.Unary.TaskEP
      (normalizedTaskUpperAge B ht i.val (taskCut B ht i) (taskResetMenu B ht i) priority)
      (normalizedTaskLowerAge B ht i.val priority) :=
  ResetOrder.Unary.abstract_reset_order_EP
    (actual_task_reset_setting B ht priority i (taskResetMenu B ht i))
    (normalized_task_full_jep B ht i.val (taskCut B ht i) (taskResetMenu B ht i) priority)
    (normalized_task_full_ramsey B ht i.val (taskCut B ht i) (taskResetMenu B ht i) priority)
    (normalized_task_midpoint_schema B ht priority i)
    (normalized_task_complete_reset_edge_type B ht i.val (taskCut B ht i)
      (taskResetMenu B ht i) priority)

end
end CCO.UnfilteredEP
