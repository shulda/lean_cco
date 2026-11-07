import CCO.UnfilteredEP.ActualTupleContracts
import CCO.UnfilteredEP.GeneratedHostOrders
import CCO.APRamseyReadout.RamseyReadout

/-!
# Actual visible relative expansion property on a fixed old host

The hidden EP witness is extended to a root-generated old host before
receiving a competitor. Every full support order on the resulting visible
host is transported onto that SAME hidden host. Hidden heredity and the
unchanged unary functions then restrict it to the prior EP witness.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
local notation "Γ" => actualTupleInterpretation B ht F

/-- Full actual readout EP relative to the terminal unary fine age.
The source expansion and then one old host precede every competitor. -/
def ActualRelativeReadoutEP
    (K : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht) → Prop) : Prop :=
  ∀ (A : FiniteInduced (X := B.Point)) (a : (Γ).ReadoutOn A),
    K (actualOrderedTemplate B ht F a) →
    ∃ E : FiniteInduced (X := B.Point),
      ∀ b : (Γ).ReadoutOn E, K (actualOrderedTemplate B ht F b) →
        Nonempty ((Γ).ReadoutEmbedding B.homogeneous a b)

/-- C84's exact actual-root consumer. Every cofinality, complete-support,
SAME-carrier lift and fine-colour map is constructed from the actual
terminal source and fixed chart. Its only order theorem input is EP of
the specified concrete hidden expansion age. -/
theorem actual_relative_readout_EP
    (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct)
    (oldAge : ∀ D, ages.oldAge D ↔ ProperFiniteCodeAge B ht D)
    (hiddenEP : ages.HiddenEP) :
    ActualRelativeReadoutEP B ht F ages.expandedAge := by
  intro A a member
  let target := actualOrderedTemplate B ht F a
  let targetOld := target.reduct (coordinateOrderExpansion B ht).toReduct
  let targetExpansion : ExpansionOn (coordinateOrderExpansion B ht).toReduct
      ages.expandedAge targetOld := ⟨target.model,rfl,member⟩
  obtain ⟨W,hW,witness⟩ := hiddenEP targetOld (ages.reductMember target member) targetExpansion
  obtain ⟨E,hE,generated,⟨inclusion⟩⟩ := actual_proper_cofinal_root_hosts B ht F W
    ((oldAge W).mp hW)
  rcases E with ⟨V,M,finiteV⟩
  let C := CCO.TerminalHiddenHN.binaryDecode (Sig B ht)
    (CCO.TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) M
  have hC : ActualAge B ht C := hE.1
  have hM : CoordinateModel B ht C = M :=
    CCO.TerminalHiddenHN.binaryStructure_binaryDecode _ _ M
  let : Finite V := finiteV
  let : Fintype V := Fintype.ofFinite V
  let : LinearOrder V := LinearOrder.lift' (Fintype.equivFin V) (Fintype.equivFin V).injective
  let R := actualHostReadout B ht F C hC
  have generatedC : RootGenerated (CoordinateModel B ht C) (tupleScheme B ht F) :=
    hM.symm ▸ generated
  let j : Structure.Embedding W.model (CoordinateModel B ht C) :=
    inclusion.targetCongr hM.symm
  refine ⟨R.old,?_⟩
  intro b competing
  let newR := reorderedHostReadout B ht F R generatedC b
  let oldE : FiniteHidden.{max u v w,max u v} (CoordinateLanguage B ht) :=
    ⟨V,CoordinateModel B ht C,inferInstance⟩
  let bE : ExpansionOn (coordinateOrderExpansion B ht).toReduct ages.expandedAge oldE := {
    model := @OrderedCoordinateModel B ht V C (generatedHostOrder B ht F R generatedC b)
    reduct_eq := rfl
    member := generated_ordered_host_member B ht F R generatedC
      ages.expandedAge ages.expandedIsoClosed b competing }
  have closed : bE.model.IsClosed (Set.range j.point) := by
    intro symbol x hx y hy
    obtain ⟨z,rfl⟩ := hx
    change y ∈ (CoordinateModel B ht C).func symbol (j.point z) at hy
    obtain ⟨q,_hq,hqy⟩ := j.reflect_func symbol z y hy
    exact ⟨q,hqy⟩
  let competitorW := ages.restrictOn bE j closed
  obtain ⟨f⟩ := witness competitorW
  let full := (ages.restrictOnEmbedding bE j closed).comp f
  exact ⟨@actualHiddenToReadout _ _ _ _ _ (generatedHostOrder B ht F R generatedC b) _ a newR full⟩

end
end CCO.UnfilteredEP
