import CCO.UnfilteredEP.OrderedMidpointActual
import CCO.UnfilteredEP.OrderedMidpointLift

/-! The actual midpoint gate for EVERY prescribed finite-member task.
The source realization, quotient points and WHOLE pair diagram lift are
all constructed here. The reset menu is the proved actual source menu. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- C66: every ordered parent pair of every actual normalized member
has a legal fresh reset midpoint. Both cylinder clauses use the SAME
source-chosen reset orbital, fixed before the competitor is supplied. -/
theorem actual_normalized_task_midpoint
    (priority : LinearOrder (Sig B ht).Sorts) (r : CutOrbit B ht)
    {V : Type (max u v)} (C : Structure (Sig B ht) V) (hC : ProperAge B ht C)
    (oC : LinearOrder V)
    (fixedC : hierarchicalOrder B ht C hC.2 hC.1 priority oC = oC)
    (x y : HiddenCutCarrier B ht C (cutRepresentative B ht r).val)
    (parent : (actualCutSystem B ht C hC.1).parent (cutRepresentative B ht r).val x y)
    (comparison : @LT.lt _ oC.toLT x.val y.val) :
    ∃ (W : Type (max u v)) (_ : Finite W)
      (D : Structure (Sig B ht) W) (hD : ProperAge B ht D)
      (oD : LinearOrder W) (f : C.Embedding D),
      hierarchicalOrder B ht D hD.2 hD.1 priority oD = oD ∧
      (∀ a b, @LT.lt _ oD.toLT (f.point a) (f.point b) ↔ @LT.lt _ oC.toLT a b) ∧
      ∃ z : W, z ∉ Set.range f.point ∧
        D.sort z = hiddenCutSort B ht (cutRepresentative B ht r).val ∧
        @LT.lt _ oD.toLT (f.point x.val) z ∧
        @LT.lt _ oD.toLT z (f.point y.val) ∧
        (CoordinateModel B ht D).binary
          (resetCylinderName B ht
            (fullMIOfNamed B (cutRepresentative B ht r).val.1 (cutRepresentative B ht r).val.2)
            (actualResetMenu B ht _)) (f.point x.val) z ∧
        (CoordinateModel B ht D).binary
          (resetCylinderName B ht
            (fullMIOfNamed B (cutRepresentative B ht r).val.1 (cutRepresentative B ht r).val.2)
            (actualResetMenu B ht _)) z (f.point y.val) := by
  let cut := (cutRepresentative B ht r).val
  let J := fullMIOfNamed B cut.1 cut.2
  let m := actualResetMenu B ht J
  obtain ⟨e⟩ := TerminalHiddenHN.actualAge_embedding (cloneSource B) (cloneHomogeneous B)
    (cloneSAP B) (fullCovers B ht) hC.1
  obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C e cut x
  obtain ⟨t,ht'⟩ := finite_cut_point_realized B ht C e cut y
  have hp : originalUpperSetoid (cloneSource B) J.val (fullMIParent B J)
      (fullMIParent_cover B J).le q t :=
    (actualCutSystem_parent_realization B ht C hC.1 e cut x y q t hq ht').mp parent
  obtain ⟨s,sx,sy,_⟩ := realized_cutPair_embedding B ht e cut q t x.val y.val hq ht'
  have before : @LT.lt _ oC.toLT (s.point (cutPairLeft B ht cut q t))
      (s.point (cutPairRight B ht cut q t)) := by
    simpa only [sx,sy] using comparison
  obtain ⟨W,finite,D,hD,oD,f,fixedD,keeps,z,fresh,sort,before,after,edge1,edge2⟩ :=
    actual_normalized_fresh_midpoint B ht priority r m q t hp C hC oC fixedC s before
  dsimp only [cut] at sx sy
  refine ⟨W,finite,D,hD,oD,f,fixedD,keeps,z,fresh,sort,?_,?_,?_,?_⟩
  · simpa only [sx] using before
  · simpa only [sy] using after
  · simpa only [sx] using edge1
  · simpa only [sy] using edge2

end
end CCO.UnfilteredEP
