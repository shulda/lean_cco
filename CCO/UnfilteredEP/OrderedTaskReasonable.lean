import CCO.UnfilteredEP.OrderedTaskPrefixExtension
import CCO.UnfilteredEP.NormalizedTaskProvider
import CCO.UnfilteredEP.TaskPrefixAge

/-! Actual single-task reasonableness. The supplied old map retains
EVERY earlier-prefix comparison. Only the next independent task is
extended, on that SAME point map; all target earlier tasks stay fixed. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 300000
set_option maxHeartbeats 1600000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section

private theorem task_witness_on_equal_old
    {L : ResetOrder.Unary.Primitive.Signature.{u}}
    {P : ResetOrder.Unary.Fibres.{u,v} L} (U : ResetOrder.Unary.TaskAge P)
    {A C : ResetOrder.Unary.TaskObject P} {D : ResetOrder.Unary.Object.{u,v} L}
    (hC : U C) (oldEq : C.old = D) (f : A.old.Emb D)
    (g : ResetOrder.Unary.TaskHom A C) (samePoint : HEq g.old.point f.point) :
    ∃ o : ResetOrder.Unary.FibreOrder P D, U ⟨D,o⟩ ∧
      ∃ h : ResetOrder.Unary.TaskHom A ⟨D,o⟩, ∀ x, h.old.point x = f.point x := by
  subst D
  exact ⟨C.order,hC,g,fun x => congrFun (eq_of_heq samePoint) x⟩

private theorem resetUnaryObject_decodeObject {L : Language.{u}}
    (A : ResetOrder.Unary.Object.{u,v} (resetUnarySignature L)) :
    resetUnaryObject L (resetUnaryDecodeObject L A) = A := by
  cases A with
  | mk V finite data =>
    change (⟨V,finite,resetUnaryStructure L (resetUnaryDecode L data)⟩ :
      ResetOrder.Unary.Object (resetUnarySignature L)) = ⟨V,finite,data⟩
    rw [resetUnaryStructure_decode]

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- C67: the actual next-task expansion is reasonable over the exact
earlier-prefix class. The target's complete old prefix and the supplied
old point map are preserved literally. -/
theorem actual_task_reasonable
    (priority : LinearOrder (Sig B ht).Sorts) (i : Fin (taskCount B ht))
    (m : ActualResetMenu B (fullMIOfNamed B (taskCut B ht i).1 (taskCut B ht i).2)) :
    ResetOrder.Unary.TaskReasonable
      (normalizedTaskUpperAge B ht i.val (taskCut B ht i) m priority)
      (resetUnaryAge (PrefixFullCodeLanguage B ht i.val)
        (NormalizedPrefixAge B ht priority i.val)) := by
  intro A hA D hD f
  obtain ⟨F,hF,equalTask⟩ := hA
  subst A
  change NormalizedPrefixAge B ht priority i.val
    (resetUnaryDecodeObject (PrefixFullCodeLanguage B ht i.val) D) at hD
  obtain ⟨target,hTarget,targetPrefix⟩ := hD
  let Q := normalizedPresentation B ht priority hTarget
  let P := normalizedPresentation B ht priority hF.normalized
  have Pmodel : normalizedTaskDecode B ht i.val (taskCut B ht i) m F =
      @OrderedCoordinateModel B ht F.task.old.Carrier P.raw P.order := P.model_eq
  have Qmodel : target = @OrderedCoordinateModel B ht D.Carrier Q.raw Q.order := Q.model_eq
  let decoded := resetUnaryDecodeEmbedding (PrefixFullCodeLanguage B ht i.val) f
  let prescribed := (decoded.sourceCongr hF.prefix_eq).targetCongr targetPrefix
  let orderedSource := prescribed.sourceCongr
    (congrArg (taskPrefixData B ht i.val) Pmodel)
  let orderedBoth := orderedSource.targetCongr
    (congrArg (taskPrefixData B ht i.val) Qmodel)
  let raw := TerminalHiddenHN.binaryEmbeddingInverse (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht))
    (orderedBoth.reduct (prefixBaseReduct B ht i.val))
  obtain ⟨new,fixedNew,prefixNew,selected⟩ := normalized_prefix_order_extension B ht priority
    P.actual Q.actual Q.proper raw P.order Q.order i i.val le_rfl
  let targetNew : FiniteHidden (OrderedCoordinateLanguage B ht) :=
    ⟨D.Carrier,@OrderedCoordinateModel B ht D.Carrier Q.raw new,D.finite⟩
  have memberNew : NormalizedProperAge B ht priority targetNew :=
    ⟨Q.raw,new,Q.actual,Q.proper,fixedNew,rfl⟩
  have newPrefix : taskPrefixData B ht i.val targetNew.model =
      resetUnaryDecode (PrefixFullCodeLanguage B ht i.val) D.data :=
    prefixNew.trans ((congrArg (taskPrefixData B ht i.val) Qmodel).symm.trans targetPrefix.symm)
  let G := normalizedTaskFullObject B ht i.val (taskCut B ht i) m priority targetNew memberNew
  have Gmember : normalizedTaskUpperAge B ht i.val (taskCut B ht i) m priority G.task :=
    ⟨G,normalizedTaskFullObject_mem B ht i.val (taskCut B ht i) m priority targetNew memberNew,rfl⟩
  have oldEq : G.task.old = D := by
    have objects : (⟨D.Carrier,taskPrefixData B ht i.val targetNew.model,D.finite⟩ :
        FiniteHidden (PrefixFullCodeLanguage B ht i.val)) =
        resetUnaryDecodeObject (PrefixFullCodeLanguage B ht i.val) D := by
      exact congrArg (fun model : Structure (PrefixFullCodeLanguage B ht i.val) D.Carrier =>
        (⟨D.Carrier,model,D.finite⟩ : FiniteHidden (PrefixFullCodeLanguage B ht i.val))) newPrefix
    exact (congrArg (resetUnaryObject (PrefixFullCodeLanguage B ht i.val)) objects).trans
      (resetUnaryObject_decodeObject D)
  let oldMap : F.task.old.Emb G.task.old := resetUnaryEmbeddingOfDecode
    (PrefixFullCodeLanguage B ht i.val) (decoded.targetCongr newPrefix.symm)
  have sourceBase : taskOldBase B ht i.val F.task.old = CoordinateModel B ht P.raw := by
    change prefixBase B ht (resetUnaryDecode (PrefixFullCodeLanguage B ht i.val) F.task.old.data) = _
    rw [hF.prefix_eq,Pmodel]
    rfl
  have preserves : ∀ x y, F.task.order.lt x y → G.task.order.lt (oldMap.point x) (oldMap.point y) := by
    intro x y h
    obtain ⟨same,comparison⟩ := (hF.comparison x y).mp h
    have sameRaw : (actualParentFormula B ht (taskCut B ht i)).same (CoordinateModel B ht P.raw) x y :=
      sourceBase ▸ same
    let xx : HiddenCutCarrier B ht P.raw (taskCut B ht i) := ⟨x,sameRaw.1⟩
    let yy : HiddenCutCarrier B ht P.raw (taskCut B ht i) := ⟨y,sameRaw.2.1⟩
    have parent := (actualParentFormula_same_iff B ht P.raw P.actual (taskCut B ht i) xx yy).mp sameRaw
    rw [Pmodel] at comparison
    have before : @LT.lt _ P.order.toLT x y := comparison.2.2
    have newComparison := (selected xx yy parent).mpr before
    have targetSame := ((actualTaskFibres B ht i.val (taskCut B ht i) m).same_natural oldMap x y).mpr same
    exact ⟨targetSame,targetSame.1,targetSame.2.1,newComparison⟩
  let g := ResetOrder.Unary.taskHomOfPreserves oldMap preserves
  exact task_witness_on_equal_old _ Gmember oldEq f g HEq.rfl

end
end CCO.UnfilteredEP
