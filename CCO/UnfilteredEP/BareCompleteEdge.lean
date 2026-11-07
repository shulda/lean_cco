import CCO.UnfilteredEP.ResetEdgeNormalized

/-!
# C37–C42 without any reset-square premise

An arbitrary complete quotient orbital is specified by its actual pair
of original representatives in one J-parent fibre. Its original-group
motion and the generic whole-pair comparison theorem determine the
complete pointed normalized type. No ActualResetMenu, RAW square,
STRONG square, hidden SAP provider, Ramsey arrow or EP is assumed.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w z z'
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.TerminalLattice CCO.TerminalPowers CCO.UnaryTermsReturn
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- Any two pairs in the SAME arbitrary complete original quotient
orbital are moved together by one original motion. No square is used. -/
theorem bare_complete_orbital_hidden_motion {i : B.Sorts}
    (J : FullCloneProperMI B.source i) (first second : CloneSAP.Carrier B.Point i)
    (q t q' t' : Quotient J.val.val)
    (hqt : originalQuotientOrbital (cloneSource B) (G := FullAut (cloneSource B))
      J.val first second q t)
    (hqt' : originalQuotientOrbital (cloneSource B) (G := FullAut (cloneSource B))
      J.val first second q' t') :
    ∃ g : (Hidden B ht).Aut,
      g • coordinateNode B ht J q = coordinateNode B ht J q' ∧
      g • coordinateNode B ht J t = coordinateNode B ht J t' := by
  let : MulAction (FullAut (cloneSource B)) (Quotient J.val.val) :=
    originalQuotientAction (cloneSource B) (cloneHomogeneous B) J.val
  obtain ⟨g,hgq,hgt⟩ := hqt
  obtain ⟨h,hhq,hht⟩ := hqt'
  have hgq' : g • Quotient.mk J.val.val first = q := hgq
  have hgt' : g • Quotient.mk J.val.val second = t := hgt
  have hhq' : h • Quotient.mk J.val.val first = q' := hhq
  have hht' : h • Quotient.mk J.val.val second = t' := hht
  let k := h*g⁻¹
  have hq : k • q = q' := by
    change (h*g⁻¹) • q = q'
    rw [mul_smul,← hgq',inv_smul_smul]
    exact hhq'
  have ht' : k • t = t' := by
    change (h*g⁻¹) • t = t'
    rw [mul_smul,← hgt',inv_smul_smul]
    exact hht'
  let motion := CCO.TypedOrbitFrames.originalCompletedMotionHom (cloneSource B) (HF B)
    (cloneSAP B) (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) k
  have value (a : Quotient J.val.val) :
      motion • coordinateNode B ht J a = coordinateNode B ht J (k • a) := by
    induction a using Quotient.inductionOn with | _ x => rfl
  exact ⟨motion,(value q).trans (congrArg (coordinateNode B ht J) hq),
    (value t).trans (congrArg (coordinateNode B ht J) ht')⟩

variable {V : Type z} {W : Type z'}
variable (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (D : CCO.UnarySupport.Structure (Sig B ht) W)
variable (hC : ActualAge B ht C) (hD : ActualAge B ht D)
variable (properC : ∀ x, ProperSort B ht (C.sort x))
variable (properD : ∀ x, ProperSort B ht (D.sort x))
variable (priority : LinearOrder (Sig B ht).Sorts) (oC : LinearOrder V) (oD : LinearOrder W)

/-- Exact generic source scope: ANY complete named relative orbital,
without its having a reset square. The one original motion preserves
all old atomic/function data, both marks and EVERY comparison on the
WHOLE generated pair support. Thus it gives one complete pointed type. -/
theorem complete_relative_orbital_normalized_pair_type
    (fixedC : hierarchicalOrder B ht C properC hC priority oC = oC)
    (fixedD : hierarchicalOrder B ht D properD hD priority oD = oD)
    (eC : C.Embedding (Target B ht)) (eD : D.Embedding (Target B ht))
    (J : HiddenCut B) (first second : CloneSAP.Carrier B.Point J.1)
    (parent : fullMIParent B (fullMIOfNamed B J.1 J.2) first second)
    (_external : ¬ J.2.val first second)
    (x y : HiddenCutCarrier B ht C J) (x' y' : HiddenCutCarrier B ht D J)
    (q t q' t' : HiddenCutPoint B J)
    (hxq : eC.point x.val = namedNode B J.2 q)
    (hyt : eC.point y.val = namedNode B J.2 t)
    (hxq' : eD.point x'.val = namedNode B J.2 q')
    (hyt' : eD.point y'.val = namedNode B J.2 t')
    (hqt : originalQuotientOrbital (cloneSource B) (G := FullAut (cloneSource B))
      J.2.val first second q t)
    (hqt' : originalQuotientOrbital (cloneSource B) (G := FullAut (cloneSource B))
      J.2.val first second q' t')
    (hxy : @LT.lt _ oC.toLT x.val y.val) (hxy' : @LT.lt _ oD.toLT x'.val y'.val) :
    ∃ g : (Hidden B ht).Aut,
      g • eC.point x.val = eD.point x'.val ∧
      g • eC.point y.val = eD.point y'.val ∧
      ∀ (z v : V) (z' v' : W),
        eD.point z' = g • eC.point z → eD.point v' = g • eC.point v →
        eC.point z ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val} →
        eC.point v ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val} →
        (@LT.lt _ oD.toLT z' v' ↔ @LT.lt _ oC.toLT z v) := by
  let fullJ := fullMIOfNamed B J.1 J.2
  obtain ⟨g,hgq,hgt⟩ := bare_complete_orbital_hidden_motion B ht fullJ first second q t q' t' hqt hqt'
  have hx : g • eC.point x.val = eD.point x'.val :=
    (congrArg (fun a => g • a) hxq).trans (hgq.trans hxq'.symm)
  have hy : g • eC.point y.val = eD.point y'.val :=
    (congrArg (fun a => g • a) hyt).trans (hgt.trans hyt'.symm)
  have upper := originalQuotientOrbital_inside_originalUpper (cloneSource B) (cloneHomogeneous B)
    J.2.val (fullMIParent B fullJ) (fullMIParent_cover B fullJ).le first second parent
  have upper_eq (a b : HiddenCutPoint B J) :
      originalUpperSetoid (cloneSource B) J.2.val (fullMIParent B fullJ)
        (fullMIParent_cover B fullJ).le a b →
      Quot.mapRight (fullMIParent_cover B fullJ).le a =
        Quot.mapRight (fullMIParent_cover B fullJ).le b := by
    induction a using Quotient.inductionOn with | _ a =>
      induction b using Quotient.inductionOn with | _ b =>
        intro hab
        exact Quotient.sound ((originalUpperSetoid_mk (cloneSource B) J.2.val
          (fullMIParent B fullJ) (fullMIParent_cover B fullJ).le a b).mp hab)
  have hp : (actualCutSystem B ht C hC).parent J x y := by
    apply (actualCutSystem_parent_realization B ht C hC eC J x y q t hxq hyt).mpr
    exact upper_eq q t (upper q t hqt)
  have hp' : (actualCutSystem B ht D hD).parent J x' y' := by
    apply (actualCutSystem_parent_realization B ht D hD eD J x' y' q' t' hxq' hyt').mpr
    exact upper_eq q' t' (upper q' t' hqt')
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
