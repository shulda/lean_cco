import CCO.UnfilteredEP.TaskSuccessorCodec
import CCO.UnfilteredEP.NormalizedHiddenEP

/-! Source C68--C70 composition with one genuine source reset menu at
every actual independent task. Empty task families need no special gate. -/
universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- This menu includes the actual source STRONG and RAW squares. -/
def taskResetMenu (i : Fin (taskCount B ht)) :=
  actualResetMenu B ht (fullMIOfNamed B (taskCut B ht i).1 (taskCut B ht i).2)

/-- Finite I12 tasks feed the actual C70 normalized expansion package.
All image classes, reducts, closure gates and final order reconstruction
are concretely bound by the prefix modules. -/
theorem actual_normalized_hidden_EP_of_unary_tasks
    (priority : LinearOrder (Sig B ht).Sorts)
    (tasks : ∀ i : Fin (taskCount B ht),
      CCO.ResetOrder.Unary.TaskEP
        (normalizedTaskUpperAge B ht i.val (taskCut B ht i) (taskResetMenu B ht i) priority)
        (resetUnaryAge (PrefixFullCodeLanguage B ht i.val)
          (NormalizedPrefixAge.{u,v,w,max u v} B ht priority i.val))) :
    (actualNormalizedExpansionAges B ht priority).HiddenEP :=
  actual_normalized_hidden_EP_of_taskSteps B ht priority
    (fun n hn => taskEP_to_prefixRelativeEP B ht priority ⟨n,hn⟩
      (taskResetMenu B ht ⟨n,hn⟩) (tasks ⟨n,hn⟩))

end
end CCO.UnfilteredEP
