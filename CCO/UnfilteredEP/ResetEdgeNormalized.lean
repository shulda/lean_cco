import CCO.UnfilteredEP.ResetEdgeTerms
import CCO.UnfilteredEP.ResetEdgeUnordered

/-! C37-C42: the one actual orbital motion of the marked reset pair
preserves every comparison on its WHOLE generated support in the
synchronized hierarchical order. All actual targets, partners and mixed
unary paths are included. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w z z'
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnaryFreshFrames
open CCO.ParityHasse.Original CCO.TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- All four comparisons of two ordered marked endpoints depend only
on their two marks. -/
theorem ordered_pairMark_iff {V : Type z} {W : Type z'}
    (oV : LinearOrder V) (oW : LinearOrder W) (x y : V) (x' y' : W)
    (hxy : @LT.lt _ oV.toLT x y) (hxy' : @LT.lt _ oW.toLT x' y') (a b : Bool) :
    @LT.lt _ oW.toLT (pairMark x' y' a) (pairMark x' y' b) ↔
      @LT.lt _ oV.toLT (pairMark x y a) (pairMark x y b) := by
  cases a <;> cases b <;> simp only [pairMark]
  · exact iff_of_false (@lt_irrefl _ oW.toPreorder x') (@lt_irrefl _ oV.toPreorder x)
  · exact iff_of_true hxy' hxy
  · exact iff_of_false (@lt_asymm _ oW.toPreorder _ _ hxy') (@lt_asymm _ oV.toPreorder _ _ hxy)
  · exact iff_of_false (@lt_irrefl _ oW.toPreorder y') (@lt_irrefl _ oV.toPreorder y)

theorem named_parent_upper_of_key (D : HiddenCut B) (q t : HiddenCutPoint B D)
    (h : Quot.mapRight (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le q =
      Quot.mapRight (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le t) :
    originalUpperSetoid (cloneSource B) D.2.val
      (fullMIParent B (fullMIOfNamed B D.1 D.2))
      (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le q t := by
  induction q using Quotient.inductionOn with | _ x =>
    induction t using Quotient.inductionOn with | _ y =>
      exact (originalUpperSetoid_mk (cloneSource B) D.2.val
        (fullMIParent B (fullMIOfNamed B D.1 D.2))
        (fullMIParent_cover B (fullMIOfNamed B D.1 D.2)).le x y).mpr (Quotient.exact h)

variable {V : Type z} {W : Type z'}
variable (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (D : CCO.UnarySupport.Structure (Sig B ht) W)
variable (hC : ActualAge B ht C) (hD : ActualAge B ht D)
variable (properC : ∀ x, ProperSort B ht (C.sort x))
variable (properD : ∀ x, ProperSort B ht (D.sort x))
variable (priority : LinearOrder (Sig B ht).Sorts) (oC : LinearOrder V) (oD : LinearOrder W)

/-- Comparison theorem for the canonical pointed motion, in arbitrary
actual finite members. Membership is in the WHOLE ambient pair closure;
no enumeration of displayed coordinates is used. -/
theorem hierarchical_pair_motion_order_iff
    (eC : C.Embedding (Target B ht)) (eD : D.Embedding (Target B ht))
    (J : HiddenCut B) (x y : HiddenCutCarrier B ht C J)
    (x' y' : HiddenCutCarrier B ht D J)
    (hp : (actualCutSystem B ht C hC).parent J x y)
    (hp' : (actualCutSystem B ht D hD).parent J x' y')
    (hxy : @LT.lt _ (hierarchicalOrder B ht C properC hC priority oC).toLT x.val y.val)
    (hxy' : @LT.lt _ (hierarchicalOrder B ht D properD hD priority oD).toLT x'.val y'.val)
    (g : (Hidden B ht).Aut)
    (hx : g • eC.point x.val = eD.point x'.val)
    (hy : g • eC.point y.val = eD.point y'.val)
    (z v : V) (z' v' : W)
    (hz : eD.point z' = g • eC.point z) (hv : eD.point v' = g • eC.point v)
    (hzmem : eC.point z ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val})
    (hvmem : eC.point v ∈ (Hidden B ht).closure {eC.point x.val,eC.point y.val}) :
    @LT.lt _ (hierarchicalOrder B ht D properD hD priority oD).toLT z' v' ↔
      @LT.lt _ (hierarchicalOrder B ht C properC hC priority oC).toLT z v := by
  have hsort (a : V) (a' : W) (ha : eD.point a' = g • eC.point a) : D.sort a' = C.sort a :=
    (eD.sort_eq a').symm.trans ((congrArg (Hidden B ht).sort ha).trans
      (((Hidden B ht).aut_sort g _).trans (eC.sort_eq a)))
  have hsz := hsort z z' hz
  have hsv := hsort v v' hv
  by_cases hs : C.sort z = C.sort v
  · obtain ⟨q,hq⟩ := finite_cut_point_realized B ht C eC J x
    obtain ⟨t,ht'⟩ := finite_cut_point_realized B ht C eC J y
    have hsAmbient : (Hidden B ht).sort (eC.point z) = (Hidden B ht).sort (eC.point v) :=
      (eC.sort_eq z).trans (hs.trans (eC.sort_eq v).symm)
    rw [hq,ht'] at hzmem hvmem
    obtain ⟨a,b,term,htermz,htermv⟩ :=
      quotient_pair_common_term B ht J q t (eC.point z) (eC.point v) hsAmbient hzmem hvmem
    let E := cutOfProperSort B ht (C.sort z) (properC z)
    have hE : (Hidden B ht).sort (eC.point z) = hiddenCutSort B ht E :=
      (eC.sort_eq z).trans (cutOfProperSort_sort B ht (C.sort z) (properC z)).symm
    let term' : Term (Lang B ht) (hiddenCutSort B ht J) (hiddenCutSort B ht E) := hE ▸ term
    have htermz' : (Hidden B ht).eval term' (namedNode B J.2 (pairMark q t a)) = eC.point z :=
      (fresh_eval_cast_output B ht hE term _).trans htermz
    have htermv' : (Hidden B ht).eval term' (namedNode B J.2 (pairMark q t b)) = eC.point v :=
      (fresh_eval_cast_output B ht hE term _).trans htermv
    have hmarks (c : Bool) : eC.point (pairMark x y c).val = namedNode B J.2 (pairMark q t c) := by
      cases c
      · exact hq
      · exact ht'
    have hgmarks (c : Bool) : g • eC.point (pairMark x y c).val = eD.point (pairMark x' y' c).val := by
      cases c
      · exact hx
      · exact hy
    have hzC : eC.point z = (Hidden B ht).eval term' (eC.point (pairMark x y a).val) := by
      rw [hmarks]
      exact htermz'.symm
    have hvC : eC.point v = (Hidden B ht).eval term' (eC.point (pairMark x y b).val) := by
      rw [hmarks]
      exact htermv'.symm
    have hzD : eD.point z' = (Hidden B ht).eval term' (eD.point (pairMark x' y' a).val) := by
      rw [hz,hzC,(Hidden B ht).aut_eval,hgmarks]
    have hvD : eD.point v' = (Hidden B ht).eval term' (eD.point (pairMark x' y' b).val) := by
      rw [hv,hvC,(Hidden B ht).aut_eval,hgmarks]
    rcases actual_terminal_quotient_term_split B ht (fullMIOfNamed B J.1 J.2) term' with bij | collapse
    · have hpab : (actualCutSystem B ht C hC).parent J (pairMark x y a) (pairMark x y b) := by
        cases a <;> cases b
        · exact (actualCutSystem B ht C hC).parent_refl _ _
        · exact hp
        · exact (actualCutSystem B ht C hC).parent_symm _ hp
        · exact (actualCutSystem B ht C hC).parent_refl _ _
      have hpab' : (actualCutSystem B ht D hD).parent J (pairMark x' y' a) (pairMark x' y' b) := by
        cases a <;> cases b
        · exact (actualCutSystem B ht D hD).parent_refl _ _
        · exact hp'
        · exact (actualCutSystem B ht D hD).parent_symm _ hp'
        · exact (actualCutSystem B ht D hD).parent_refl _ _
      have hCterm := hierarchicalOrder_bijective_term_parent B ht C hC properC priority oC eC
        J E term' bij (pairMark x y a) (pairMark x y b) hpab z v hzC hvC
      have hDterm := hierarchicalOrder_bijective_term_parent B ht D hD properD priority oD eD
        J E term' bij (pairMark x' y' a) (pairMark x' y' b) hpab' z' v' hzD hvD
      simp only [pairMark_subtype_val] at hCterm hDterm
      exact hDterm.trans ((ordered_pairMark_iff
        (hierarchicalOrder B ht C properC hC priority oC)
        (hierarchicalOrder B ht D properD hD priority oD)
        x.val y.val x'.val y'.val hxy hxy' a b).trans hCterm.symm)
    · let parent := originalUpperSetoid (cloneSource B) J.2.val
        (fullMIParent B (fullMIOfNamed B J.1 J.2))
        (fullMIParent_cover B (fullMIOfNamed B J.1 J.2)).le
      have hparent := named_parent_upper_of_key B J q t
        ((actualCutSystem_parent_realization B ht C hC eC J x y q t hq ht').mp hp)
      have hpab : originalUpperSetoid (cloneSource B) J.2.val
          (fullMIParent B (fullMIOfNamed B J.1 J.2))
          (fullMIParent_cover B (fullMIOfNamed B J.1 J.2)).le
          (pairMark q t a) (pairMark q t b) := by
        cases a <;> cases b
        · exact parent.refl _
        · exact hparent
        · exact parent.symm hparent
        · exact parent.refl _
      have he : z = v := eC.injective
        (htermz'.symm.trans ((collapse _ _ hpab).trans htermv'))
      have he' : z' = v' := eD.injective (hz.trans ((congrArg (fun p => g • eC.point p) he).trans hv.symm))
      rw [he,he']
      exact iff_of_false (@lt_irrefl _ (hierarchicalOrder B ht D properD hD priority oD).toPreorder _)
        (@lt_irrefl _ (hierarchicalOrder B ht C properC hC priority oC).toPreorder _)
  · have hs' : D.sort z' ≠ D.sort v' := fun h => hs (hsz.symm.trans (h.trans hsv))
    exact (hierarchicalOrder_different_sort B ht D properD hD priority oD z' v' hs').trans
      ((by rw [hsz,hsv] : @LT.lt _ priority.toLT (D.sort z') (D.sort v') ↔
        @LT.lt _ priority.toLT (C.sort z) (C.sort v)).trans
          (hierarchicalOrder_different_sort B ht C properC hC priority oC z v hs).symm)

end
end CCO.UnfilteredEP
