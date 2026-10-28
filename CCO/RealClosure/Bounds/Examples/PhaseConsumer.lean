import CCO.RealClosure.Bounds.Examples.PhaseCorner

/-! C32–34 as one actual infinite-source export: no finite snapshot and no
undischarged source, packet, action, CCO or nonexactness provider. -/
universe z
namespace CCO.RealClosure.Bounds.Examples.Phase
open ParityHasse.Original RealHull.Geometry

theorem infinite_phase_source : Infinite Point := inferInstance

theorem phase_counterexample_source :
    HomogeneousSource source Aut ∧ AgeAP source ∧ SemanticCCO.{0,0,z,0} source ∧
    Nat.card Colour = 7 ∧ finitePacket source homogeneous = packetEq ∧
    (∀ x : Point, Nat.card (ClassPoint source () (finitePacket source homogeneous) x) = 2) ∧
    (∀ (A : Finset Point) (x y : Point), x ∈ Acl Aut A →
      finitePacket source homogeneous x y → y ∈ Acl Aut A) ∧
    origin ∈ Dcl Aut ({a,b} : Finset Point) ∧
    origin ∈ Acl Aut ({a,b} : Finset Point) ∧
    (¬ ∃ y ∈ ({a,b} : Finset Point), finitePacket source homogeneous y origin) ∧
    (¬ ExactCRT.IsExactEq source (i := ()) (finitePacket source homogeneous).val) ∧
    (¬ ExactCRT.IsExactEq source (i := ()) rowEq.val) ∧
    (¬ ExactCRT.IsExactEq source (i := ()) columnEq.val) ∧
    ExactCRT.IsExactEq source (i := ()) rowPhaseEq.val ∧
    ExactCRT.IsExactEq source (i := ()) columnPhaseEq.val ∧
    {y : Point | gammaEq source p a y ∧ gammaEq source q b y} = {origin} ∧
    ¬ AgeSAP source := by
  refine ⟨homogeneous,ageAP,semanticCCO,?_,finitePacket_eq,?_,?_,corner_definable,
    corner_algebraic,corner_outside_finitePacket,finitePacket_not_exact,row_not_exact,
    column_not_exact,rowPhase_exact,columnPhase_exact,canonical_corner_singleton,notSAP⟩
  · simpa only [Nat.card_eq_fintype_card] using colour_card
  · intro x
    rw [finitePacket_eq]
    exact packet_card x
  · intro A x y hx hxy
    rw [finitePacket_eq] at hxy
    exact acl_packet_saturated A hx hxy
end CCO.RealClosure.Bounds.Examples.Phase
