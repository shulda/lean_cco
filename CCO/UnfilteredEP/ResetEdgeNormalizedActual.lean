import CCO.UnfilteredEP.ResetEdgeNormalized
import CCO.UnfilteredEP.TaskFormula

/-! Actual source discharge for the normalized complete reset edge:
one complete quotient orbital supplies the pointed motion, and the
proved whole-support comparison theorem supplies every order relation. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w z z'
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable {V : Type z} {W : Type z'}
variable (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (D : CCO.UnarySupport.Structure (Sig B ht) W)
variable (hC : ActualAge B ht C) (hD : ActualAge B ht D)
variable (properC : ∀ x, ProperSort B ht (C.sort x))
variable (properD : ∀ x, ProperSort B ht (D.sort x))
variable (priority : LinearOrder (Sig B ht).Sorts) (oC : LinearOrder V) (oD : LinearOrder W)

/-- Any two positively oriented edges of the SAME actual complete
reset menu have the same WHOLE normalized pointed type. The comparison
clause concerns all generated points in arbitrary finite members. -/
theorem actual_reset_normalized_pair_motion
    (fixedC : hierarchicalOrder B ht C properC hC priority oC = oC)
    (fixedD : hierarchicalOrder B ht D properD hD priority oD = oD)
    (eC : C.Embedding (Target B ht)) (eD : D.Embedding (Target B ht))
    (J : HiddenCut B) (m : ActualResetMenu B (fullMIOfNamed B J.1 J.2))
    (x y : HiddenCutCarrier B ht C J) (x' y' : HiddenCutCarrier B ht D J)
    (hr : (actualCutFormula B ht J m).reset (CoordinateModel B ht C) x.val y.val)
    (hr' : (actualCutFormula B ht J m).reset (CoordinateModel B ht D) x'.val y'.val)
    (hxy : @LT.lt _ oC.toLT x.val y.val) (hxy' : @LT.lt _ oD.toLT x'.val y'.val) :
    ∃ g : (Hidden B ht).Aut,
      g • eC.point x.val = eD.point x'.val ∧
      g • eC.point y.val = eD.point y'.val ∧
      ∀ (z v : V) (z' v' : W),
        eD.point z' = g • eC.point z → eD.point v' = g • eC.point v →
        eC.point z ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val} →
        eC.point v ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val} →
        (@LT.lt _ oD.toLT z' v' ↔ @LT.lt _ oC.toLT z v) := by
  obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C eC J x
  obtain ⟨t,ht'⟩ := finite_cut_point_realized B ht C eC J y
  obtain ⟨q',hq'⟩ := finite_cut_point_realized B ht D eD J x'
  obtain ⟨t',ht''⟩ := finite_cut_point_realized B ht D eD J y'
  have hRel := (actualCutFormula_reset_realization B ht C eC J m x y q t hq ht').mp hr
  have hRel' := (actualCutFormula_reset_realization B ht D eD J m x' y' q' t' hq' ht'').mp hr'
  obtain ⟨g,hgq,hgt⟩ := actual_reset_hidden_pairs_move B ht
    (fullMIOfNamed B J.1 J.2) m q t q' t' hRel hRel'
  have hx : g • eC.point x.val = eD.point x'.val :=
    (congrArg (fun p => g • p) hq).trans (hgq.trans hq'.symm)
  have hy : g • eC.point y.val = eD.point y'.val :=
    (congrArg (fun p => g • p) ht').trans (hgt.trans ht''.symm)
  have hp := (actualParentFormula_same_iff B ht C hC J x y).mp
    (actualCutFormula_reset_same B ht C hC eC J m x.val y.val hr)
  have hp' := (actualParentFormula_same_iff B ht D hD J x' y').mp
    (actualCutFormula_reset_same B ht D hD eD J m x'.val y'.val hr')
  refine ⟨g,hx,hy,?_⟩
  intro z v z' v' hz hv hzmem hvmem
  have hxyN := (Iff.of_eq (congrArg (fun o : LinearOrder V => @LT.lt _ o.toLT x.val y.val) fixedC)).mpr hxy
  have hxyN' := (Iff.of_eq (congrArg (fun o : LinearOrder W => @LT.lt _ o.toLT x'.val y'.val) fixedD)).mpr hxy'
  have h := hierarchical_pair_motion_order_iff B ht C D hC hD properC properD priority oC oD
    eC eD J x y x' y' hp hp' hxyN hxyN' g hx hy z v z' v' hz hv hzmem hvmem
  exact (Iff.of_eq (congrArg (fun o : LinearOrder W => @LT.lt _ o.toLT z' v') fixedD)).symm.trans
    (h.trans (Iff.of_eq (congrArg (fun o : LinearOrder V => @LT.lt _ o.toLT z v) fixedC)))

end
end CCO.UnfilteredEP
