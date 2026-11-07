import CCO.UnfilteredEP.OrderedMidpointTask
import CCO.UnfilteredEP.ResetEdgeTaskPresentation
import CCO.UnfilteredEP.NormalizedTaskMaps
import CCO.UnfilteredEP.NormalizedTaskComposition

/-! Actual C66 midpoint schema in the ONE full normalized task provider.
The whole supplied old member embeds, the midpoint is fresh over its
entire image, and both legs retain the canonical complete reset menu. -/
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1500000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts) (i : Fin (taskCount B ht))
local notation "J" => taskCut B ht i
local notation "m" => taskResetMenu B ht i
local notation "P" => actualTaskFibres B ht i.val J m

/-- No midpoint, freshness, closure or ordering gate remains assumed:
the actual normalized source construction supplies this B036 schema. -/
theorem normalized_task_midpoint_schema :
    ResetOrder.Unary.MidpointSchema
      (normalizedTaskFullAge B ht i.val J m priority) := by
  intro A hA u v huv
  let Q := normalizedPresentation B ht priority hA.normalized
  have hs := ((hA.comparison u v).mp huv).1
  rw [normalizedTaskBase_presentation B ht i.val J m priority hA] at hs
  let x : HiddenCutCarrier B ht Q.raw J := ⟨u,hs.1⟩
  let y : HiddenCutCarrier B ht Q.raw J := ⟨v,hs.2.1⟩
  have parent := (actualParentFormula_same_iff B ht Q.raw Q.actual J x y).mp hs
  have comparison := normalizedTask_comparison_global B ht i.val J m priority hA u v huv
  obtain ⟨W,finite,D,hD,oD,f,fixedD,keeps,z,fresh,sz,before,after,edge1,edge2⟩ :=
    actual_normalized_task_midpoint B ht priority (taskEnumeration B ht i)
      Q.raw ⟨Q.actual,Q.proper⟩ Q.order Q.fixed x y parent comparison
  let : Finite W := finite
  let : LinearOrder A.task.old.Carrier := Q.order
  let : LinearOrder (normalizedTaskHidden B ht i.val J m A).Carrier := Q.order
  let : LinearOrder W := oD
  let HD : FiniteHidden (OrderedCoordinateLanguage B ht) :=
    ⟨W,@OrderedCoordinateModel B ht W D oD,finite⟩
  have hHD : NormalizedProperAge B ht priority HD :=
    ⟨D,oD,hD.1,hD.2,fixedD,rfl⟩
  let T := normalizedTaskFullObject B ht i.val J m priority HD hHD
  have hT : normalizedTaskFullAge B ht i.val J m priority T :=
    normalizedTaskFullObject_mem B ht i.val J m priority HD hHD
  let ordered : CCO.UnaryHN.Raw.OrderedEmbedding Q.raw D := ⟨f,keeps⟩
  let full := CCO.TerminalHiddenHN.orderedEmbedding (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) ordered
  let coded := (full.sourceCongr Q.model_eq.symm).targetCongr
    (normalizedTaskDecode_fullObject B ht i.val J m priority HD hHD).symm
  let embedding := normalizedTaskMapOfDecode B ht i.val J m priority hA hT coded
  have point (a : A.task.old.Carrier) : embedding.point a = f.point a := rfl
  have reset1 : (P).reset T.task.old (f.point u) z := edge1
  have reset2 : (P).reset T.task.old z (f.point v) := edge2
  have same1 := (P).reset_same T.task.old T.task.order.valid (f.point u) z reset1
  have same2 := (P).reset_same T.task.old T.task.order.valid z (f.point v) reset2
  have lt1 : T.task.order.lt (f.point u) z := ⟨same1,same1.1,same1.2.1,before⟩
  have lt2 : T.task.order.lt z (f.point v) := ⟨same2,same2.1,same2.2.1,after⟩
  refine ⟨T,hT,embedding,z,?_,?_,?_,?_,?_⟩
  · exact fresh
  · rw [point]
    exact lt1
  · rw [point]
    exact lt2
  · rw [point]
    exact reset1
  · rw [point]
    exact reset2

end
end CCO.UnfilteredEP
