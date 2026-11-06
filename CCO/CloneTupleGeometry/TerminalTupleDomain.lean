import CCO.CloneTupleGeometry.OwnerTerminalGeometry
import CCO.CloneTupleGeometry.PureSpectrum

/-! At the actual safe tower endpoint, the finite clone-atom spectrum
tests define precisely the compatible full-MI tuples. Genuine terminal
RAW exactness discharges class Helly on the new clone source. Every
compatible tuple therefore represents exactly one actual owner, including
the one-coordinate case and repeated hidden coordinate values. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.CloneTupleGeometry.OwnerStage
open ParityHasse.Original TransitionClosure ExactCRT
noncomputable section
variable (B : OwnerStage.{u,v,w}) (i : B.Sorts)

/-- The fixed finite conjunction of complete semantic mixed spectrum
tests. Same-hidden-sort diagonal values use their actual full spectrum. -/
def TupleCompatible (q : FullCloneMITuple B.source i) : Prop :=
  ∀ J L : FullCloneProperMI B.source i,
    Sum.inr ⟨rfl⟩ ∈ originalTypedQuotientPairSpectrum (CloneSAP.source B.source)
      J.val L.val (q J) (q L)

theorem owner_tuple_compatible (x : B.Point i) :
    B.TupleCompatible i (originalOwnerMITuple B.source i x) :=
  pure_clone_original_owner_MI_spectrum_c B.source i x

/-- All coordinate classes coexist in ONE actual clone source. The
resulting owner need not be a vertex of a presented hidden finite object. -/
theorem compatible_tuple_realized (ht : B.Terminal)
    (q : FullCloneMITuple B.source i) (hq : B.TupleCompatible i q) :
    ∃ x : B.Point i, originalOwnerMITuple B.source i x = q := by
  classical
  let E : FullCloneProperMI B.source i →
      ExactEq (CloneSAP.source B.source) (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.CCO.cco_forward B.source B.cco) i :=
    fun J => ⟨J.val.val,B.terminal_MI_exact ht i J⟩
  let centre : FullCloneProperMI B.source i → CloneSAP.Carrier B.Point i :=
    fun J => (q J).out
  have hc (J : FullCloneProperMI B.source i) :
      Quotient.mk J.val.val (centre J) = q J := Quotient.out_eq _
  have hp (J L : FullCloneProperMI B.source i) :
      ∃ x, (E J).val (centre J) x ∧ (E L).val (centre L) x := by
    obtain ⟨x,hJ,hL⟩ :=
      (pure_clone_quotient_spectrum_c_iff_intersection B.source i J.val L.val
        (fullCloneKernel_le_nonidentity B.source i J.val J.property.1)
        (fullCloneKernel_le_nonidentity B.source i L.val L.property.1) (q J) (q L)).mp (hq J L)
    exact ⟨x,Quotient.exact ((hc J).trans hJ.symm),
      Quotient.exact ((hc L).trans hL.symm)⟩
  obtain ⟨x,hx⟩ := exactEq_classHelly (CloneSAP.source B.source)
    (CloneSAP.homogeneous B.source B.homogeneous) (CloneSAP.CCO.cco_forward B.source B.cco) E centre hp
  refine ⟨x.1,?_⟩
  calc
    originalOwnerMITuple B.source i x.1 = fullCloneMITuple B.source i x :=
      originalOwnerMITuple_eq_clone B.source i x.1 x.2
    _ = q := by
      funext J
      exact (Quotient.sound (J.val.val.symm (hx J))).trans (hc J)

/-- Precise terminal MI domain: the finite pair tests are equivalent to
one unique owner, rather than a merely formally compatible tuple. -/
theorem terminal_tuple_domain (ht : B.Terminal) (q : FullCloneMITuple B.source i) :
    (∃! x : B.Point i, originalOwnerMITuple B.source i x = q) ↔ B.TupleCompatible i q := by
  constructor
  · rintro ⟨x,hx,_⟩
    rw [← hx]
    exact B.owner_tuple_compatible i x
  · intro hq
    obtain ⟨x,hx⟩ := B.compatible_tuple_realized i ht q hq
    exact ⟨x,hx,fun y hy => originalOwnerMITuple_injective B.source i (hy.trans hx.symm)⟩

end
end CCO.CloneTupleGeometry.OwnerStage
