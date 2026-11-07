import CCO.UnfilteredEP.NormalizedTaskReversal
import CCO.UnfilteredEP.NormalizedTaskSettingFields
import CCO.UnfilteredEP.OrderedTaskReasonable

/-! C67--C68: every structural hypothesis of the accepted relative
reset-order criterion is discharged on the actual normalized provider.
No intermediate Ramsey property or stronger source hypothesis occurs. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- One actual representative task, retaining all earlier-prefix
relations and literally every old partial unary function. -/
theorem actual_task_reset_setting
    (priority : LinearOrder (Sig B ht).Sorts) (i : Fin (taskCount B ht))
    (m : ActualResetMenu B (fullMIOfNamed B (taskCut B ht i).1 (taskCut B ht i).2)) :
    ResetOrder.Unary.ResetSetting
      (normalizedTaskFullAge B ht i.val (taskCut B ht i) m priority)
      (normalizedTaskUpperAge B ht i.val (taskCut B ht i) m priority)
      (normalizedTaskLowerAge B ht i.val priority) where
  full_hereditary := normalized_task_full_hereditary B ht i.val (taskCut B ht i) m priority
  upper_hereditary := normalized_task_upper_hereditary B ht i.val (taskCut B ht i) m priority
  lower_hereditary := normalized_task_lower_hereditary B ht i.val priority
  reasonable := actual_task_reasonable B ht priority i m
  precompact := normalized_task_precompact B ht i.val (taskCut B ht i) m priority
  reduct := normalized_task_reduct B ht i.val (taskCut B ht i) m priority
  onto := normalized_task_onto B ht i.val (taskCut B ht i) m priority
  full_reduct := normalized_task_full_reduct B ht i.val (taskCut B ht i) m priority
  full_lift := normalized_task_full_lift B ht i.val (taskCut B ht i) m priority
  reversal := normalizedTaskUpperAge_reverse B ht i m priority

end
end CCO.UnfilteredEP
