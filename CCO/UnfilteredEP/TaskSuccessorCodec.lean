import CCO.UnfilteredEP.TaskSuccessorLanguage
import CCO.UnfilteredEP.TaskTower
import CCO.UnfilteredEP.NormalizedTaskProvider

/-! Exact ALL-map codec from one actual unary-reset task to its literal
successor prefix. No carrier, function graph or old relation is changed. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w a b
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section

private theorem taskObject_cast_old_eq
    {S : ResetOrder.Unary.Primitive.Signature.{a}}
    {P : ResetOrder.Unary.Fibres.{a,b} S}
    (A : ResetOrder.Unary.TaskObject P) {B : ResetOrder.Unary.Object.{a,b} S}
    (h : A.old = B) :
    (⟨B,h ▸ A.order⟩ : ResetOrder.Unary.TaskObject P) = A := by
  cases A with | mk old order => cases h; rfl

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)
variable (i : Fin (taskCount B ht))
variable (m : ActualResetMenu B (fullMIOfNamed B (taskCut B ht i).1 (taskCut B ht i).2))
local notation "L" => PrefixFullCodeLanguage B ht i.val
local notation "P" => actualTaskFibres B ht i.val (taskCut B ht i) m
local notation "U" => normalizedTaskUpperAge B ht i.val (taskCut B ht i) m priority

/-- Every actual task embedding is the successor embedding on the
literal same old map. Earlier task comparisons stay in its old part. -/
def normalizedTaskHomToSuccessorPrefix
    (C D : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht))
    (hC : NormalizedProperAge B ht priority C) (hD : NormalizedProperAge B ht priority D)
    (f : ResetOrder.Unary.TaskHom
      (normalizedTaskFullObject B ht i.val (taskCut B ht i) m priority C hC).task
      (normalizedTaskFullObject B ht i.val (taskCut B ht i) m priority D hD).task) :
    Structure.Embedding (taskPrefixData B ht (i.val+1) C.model)
      (taskPrefixData B ht (i.val+1) D.model) := by
  let old := resetUnaryDecodeEmbedding L f.old
  let old' := (old.sourceCongr (taskPrefixData_reduct B ht (Nat.le_succ i.val) C.model).symm).targetCongr
    (taskPrefixData_reduct B ht (Nat.le_succ i.val) D.model).symm
  exact successorPrefixEmbeddingOfTask B ht i old' (fun x y => f.order_iff x y)

/-- The actual I12 statement becomes the precise relative EP of this
one prefix step; every arbitrary successor competitor is received. -/
theorem taskEP_to_prefixRelativeEP
    (taskEP : ResetOrder.Unary.TaskEP U
      (resetUnaryAge L (NormalizedPrefixAge.{u,v,w,max u v} B ht priority i.val))) :
    ResetOrder.Generic.RelativeEP (taskTowerStep B ht i.val)
      (taskTowerClass.{u,v,w,max u v} B ht priority (i.val+1))
      (taskTowerClass B ht priority i.val) := by
  intro A hA
  obtain ⟨C,hC,hAC⟩ := hA
  let CF : FiniteHidden (OrderedCoordinateLanguage B ht) := ⟨A.Carrier,C,A.finite⟩
  let FC := normalizedTaskFullObject B ht i.val (taskCut B ht i) m priority CF hC
  have hFC : normalizedTaskFullAge B ht i.val (taskCut B ht i) m priority FC :=
    normalizedTaskFullObject_mem B ht i.val (taskCut B ht i) m priority CF hC
  obtain ⟨host,hhost,witness⟩ := taskEP FC.task ⟨FC,hFC,rfl⟩
  let H : ResetOrder.Generic.Object (taskTowerLanguage B ht i.val) :=
    resetObject L (resetUnaryDecodeObject L host)
  refine ⟨H,hhost,?_⟩
  intro E
  obtain ⟨D,hD,hED⟩ := E.member
  let DF : FiniteHidden (OrderedCoordinateLanguage B ht) := ⟨host.Carrier,D,host.finite⟩
  let FD := normalizedTaskFullObject B ht i.val (taskCut B ht i) m priority DF hD
  have hFD : normalizedTaskFullAge B ht i.val (taskCut B ht i) m priority FD :=
    normalizedTaskFullObject_mem B ht i.val (taskCut B ht i) m priority DF hD
  change resetDecode (PrefixFullCodeLanguage B ht (i.val+1)) E.data =
    taskPrefixData B ht (i.val+1) D at hED
  have prefixEq : taskPrefixData B ht i.val D = resetUnaryDecode L host.data := by
    have hh := congrArg (resetDecode L) E.reduct_eq
    rw [taskTowerInclusion_decode] at hh
    exact (taskPrefixData_reduct B ht (Nat.le_succ i.val) D).symm.trans
      ((congrArg (fun M : Structure (PrefixFullCodeLanguage B ht (i.val+1)) host.Carrier =>
        M.reduct (prefixInclusion B ht (Nat.le_succ i.val))) hED).symm.trans hh)
  have oldData : (normalizedTaskOld B ht i.val DF).data = host.data :=
    (congrArg (resetUnaryStructure L) prefixEq).trans (resetUnaryStructure_decode L host.data)
  have oldEq : (normalizedTaskOld B ht i.val DF) = host :=
    congrArg (fun d => (⟨host.Carrier,host.finite,d⟩ : ResetOrder.Unary.Object (TaskOldSignature B ht i.val))) oldData
  let order : ResetOrder.Unary.FibreOrder P host := oldEq ▸ FD.task.order
  have targetEq : (⟨host,order⟩ : ResetOrder.Unary.TaskObject P) = FD.task :=
    taskObject_cast_old_eq FD.task oldEq
  have targetMem : U ⟨host,order⟩ := targetEq.symm ▸ (show U FD.task from ⟨FD,hFD,rfl⟩)
  obtain ⟨f⟩ := witness order targetMem
  let f' : ResetOrder.Unary.TaskHom FC.task FD.task := targetEq ▸ f
  let full := normalizedTaskHomToSuccessorPrefix B ht priority i m CF DF hC hD f'
  let coded := (full.sourceCongr hAC.symm).targetCongr hED.symm
  exact ⟨resetEmbeddingOfDecode _ coded⟩

end
end CCO.UnfilteredEP
