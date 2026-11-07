import CCO.UnfilteredEP.ResetMidpoint
import CCO.UnfilteredEP.ProperFiniteClosure
import CCO.UnfilteredEP.QuotientPairClosure
import CCO.APRamseyReadout.CoordinateBridge

/-! C52-C58: the actual terminal reset produces an allowed finite
unexpanded witness over the WHOLE generated pair. The midpoint is
outside that entire base, including every term-generated partner.
No assertion about choosing compatible orders is included here. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ParityHasse.Original
open CCO.UnaryTermsReturn CCO.TerminalLattice
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- All three actual J points and their FULL named unary closures
belong to one genuine proper hidden-age object. -/
theorem actual_reset_closed_pair_witness {i : B.Sorts}
    (J : FullCloneProperMI B.source i) (m : ActualResetMenu B J)
    (q t : Quotient J.val.val)
    (hparent : originalUpperSetoid (cloneSource B) J.val (fullMIParent B J)
      (fullMIParent_cover B J).le q t) :
    ∃ z : Quotient J.val.val, m.relation q z ∧ m.relation z t ∧
      coordinateNode B ht J z ∉ (Target B ht).closure
        {coordinateNode B ht J q,coordinateNode B ht J t} ∧
      ProperAge B ht ((Target B ht).closureStructure
        {coordinateNode B ht J q,coordinateNode B ht J t,coordinateNode B ht J z}) := by
  obtain ⟨z,hqz,hzt,hzq,hzt',_⟩ := m.midpoint q t hparent
  refine ⟨z,hqz,hzt,?_,?_⟩
  · exact quotient_third_point_outside_partial_pair_closure
      (cloneSource B) (HF B) (cloneSAP B)
      (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht))
      (fun _ E F hEF x => B.terminal_interval_infinite ht E F hEF x)
      (namedCoordinateHF B ht i J) q t z hzq hzt'
  · apply proper_target_closure_member B ht
    · exact ((Set.finite_singleton (coordinateNode B ht J z)).insert
        (coordinateNode B ht J t)).insert (coordinateNode B ht J q)
    · intro x hx
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl <;> trivial

end
end CCO.UnfilteredEP
