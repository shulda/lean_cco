import CCO.UnfilteredEP.ResetEdgeNormalizedActual
import CCO.UnfilteredEP.ResetEdgeSupportIso
import CCO.UnfilteredEP.ResetEdgeTaskPresentation
import CCO.UnfilteredEP.NormalizedTaskMaps
import CCO.UnfilteredEP.TaskClosure

/-! The complete source edge comparison gives a surjective full task
isomorphism, including every prefix relation and every global comparison.
Both objects have their actual entire two-root-generated supports. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1500000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)
variable (J : HiddenCut B) (m : ActualResetMenu B (fullMIOfNamed B J.1 J.2))
variable (priority : LinearOrder (Sig B ht).Sorts)
variable {A C : ResetOrder.Unary.FullObject (actualTaskFibres B ht n J m) (normalizedTaskExtra B ht n)}
variable (hA : normalizedTaskFullAge B ht n J m priority A)
variable (hC : normalizedTaskFullAge B ht n J m priority C)

/-- Full and old function closures are literally the actual raw closure. -/
theorem normalizedTask_generated_raw (x y : A.task.old.Carrier)
    (generated : A.unary.closure {x,y} = Set.univ) :
    (normalizedPresentation B ht priority hA.normalized).raw.closure {x,y} = Set.univ := by
  exact (congrArg (fun R : CCO.UnarySupport.Structure (Sig B ht) A.task.old.Carrier =>
    R.closure {x,y}) (normalizedTaskRaw_presentation B ht n J m priority hA)).symm.trans
      ((taskOldRaw_closure B ht n A.task.old {x,y}).trans
        ((full_closure_eq_old A {x,y}).symm.trans generated))

/-- Any vertex of a generated member lies in its WHOLE ambient pair
closure under an arbitrary supplied actual realization. -/
theorem generated_ambient_pair_mem
    {V : Type (max u v)} (R : CCO.UnarySupport.Structure (Sig B ht) V)
    (e : R.Embedding (Target B ht)) (x y z : V)
    (generated : R.closure {x,y} = Set.univ) :
    e.point z ∈ (Hidden B ht).closure {e.point x,e.point y} := by
  have hz : e.point z ∈ e.point '' R.closure {x,y} :=
    ⟨z,generated.symm ▸ Set.mem_univ z,rfl⟩
  rw [support_embedding_closure_image e] at hz
  simp only [Set.image_insert_eq,Set.image_singleton] at hz
  exact actual_partial_closure_eq (cloneSource B) (HF B) (cloneSAP B)
    (TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) _ ▸ hz

include hA hC in
/-- C37-C42 in the actual full task provider: the complete pointed
normalized type of a positively oriented reset edge is unique. -/
theorem normalized_task_generated_edge_iso
    (x y : A.task.old.Carrier) (x' y' : C.task.old.Carrier)
    (generatedA : A.unary.closure {x,y} = Set.univ)
    (generatedC : C.unary.closure {x',y'} = Set.univ)
    (hxy : A.task.order.lt x y)
    (hxy' : C.task.order.lt x' y')
    (hreset : (actualTaskFibres B ht n J m).reset A.task.old x y)
    (hreset' : (actualTaskFibres B ht n J m).reset C.task.old x' y') :
    ∃ f : ResetOrder.Unary.FullIso A C, f.hom.point x = x' ∧ f.hom.point y = y' := by
  let QA := normalizedPresentation B ht priority hA.normalized
  let QC := normalizedPresentation B ht priority hC.normalized
  have genA := normalizedTask_generated_raw B ht n J m priority hA x y generatedA
  have genC := normalizedTask_generated_raw B ht n J m priority hC x' y' generatedC
  obtain ⟨eA⟩ := QA.actual.2
  obtain ⟨eC⟩ := QC.actual.2
  have hrA := normalizedTask_reset_presentation B ht n J m priority hA x y hreset
  have hrC := normalizedTask_reset_presentation B ht n J m priority hC x' y' hreset'
  have hsA := (actualCutFormula B ht J m).reset_sorted (CoordinateModel B ht QA.raw) hrA
  have hsC := (actualCutFormula B ht J m).reset_sorted (CoordinateModel B ht QC.raw) hrC
  let xd : HiddenCutCarrier B ht QA.raw J := ⟨x,hsA.1⟩
  let yd : HiddenCutCarrier B ht QA.raw J := ⟨y,hsA.2⟩
  let xd' : HiddenCutCarrier B ht QC.raw J := ⟨x',hsC.1⟩
  let yd' : HiddenCutCarrier B ht QC.raw J := ⟨y',hsC.2⟩
  obtain ⟨g,hgx,hgy,horder⟩ := actual_reset_normalized_pair_motion B ht QA.raw QC.raw
    QA.actual QC.actual QA.proper QC.proper priority QA.order QC.order QA.fixed QC.fixed
    eA eC J m xd yd xd' yd' hrA hrC
    (normalizedTask_comparison_global B ht n J m priority hA x y hxy)
    (normalizedTask_comparison_global B ht n J m priority hC x' y' hxy')
  obtain ⟨raw,hraw,hx,hy⟩ := realized_generated_pair_iso eA eC (partialAutIso (Hidden B ht) g)
    x y x' y' genA genC hgx hgy
  have compare (z v) : @LT.lt _ QC.order.toLT (raw.equiv z) (raw.equiv v) ↔
      @LT.lt _ QA.order.toLT z v :=
    horder z v (raw.equiv z) (raw.equiv v) (hraw z) (hraw v)
      (generated_ambient_pair_mem B ht QA.raw eA x y z genA)
      (generated_ambient_pair_mem B ht QA.raw eA x y v genA)
  let old := TerminalHiddenHN.binaryEmbedding (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht))
    raw.toEmbedding
  let ordered : Structure.Embedding (@OrderedCoordinateModel B ht A.task.old.Carrier QA.raw QA.order)
      (@OrderedCoordinateModel B ht C.task.old.Carrier QC.raw QC.order) := {
    point := raw.equiv
    injective := raw.equiv.injective
    sort_eq := raw.sort_eq
    map_func := raw.toEmbedding.map_func
    reflect_func := raw.toEmbedding.reflect_func
    unary_iff := fun U => PEmpty.elim U
    binary_iff := by
      intro R z v
      cases R with
      | inl R => exact old.binary_iff R z v
      | inr p =>
        change (QC.raw.sort (raw.equiv z) = p.1 ∧ QC.raw.sort (raw.equiv v) = p.2 ∧
          @LT.lt _ QC.order.toLT (raw.equiv z) (raw.equiv v)) ↔
          (QA.raw.sort z = p.1 ∧ QA.raw.sort v = p.2 ∧ @LT.lt _ QA.order.toLT z v)
        rw [raw.sort_eq,raw.sort_eq]
        exact and_congr Iff.rfl (and_congr Iff.rfl (compare z v)) }
  let decoded := FullEmbedding.castModels ordered QA.model_eq.symm QC.model_eq.symm
  let f := normalizedTaskMapOfDecode B ht n J m priority hA hC decoded
  have fpoint (z) : f.point z = raw.equiv z := by
    change decoded.point z = raw.equiv z
    exact FullEmbedding.castModels_point _ _ _ z
  refine ⟨⟨f,?_⟩,(fpoint x).trans hx,(fpoint y).trans hy⟩
  intro z
  refine ⟨raw.equiv.symm z,?_⟩
  exact (fpoint _).trans (raw.equiv.apply_symm_apply z)

end
end CCO.UnfilteredEP
