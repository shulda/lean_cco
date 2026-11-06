import CCO.ExactEPGeometry.OldGatePivotBridge
import CCO.ExactEPGeometry.ActualPhaseMaximalGate
import CCO.ExactEPGeometry.CertifiedGateTower

/-! Receive an EXISTING actual source phase, retaining its own complete
character and successor. Its genuine maximal gate is lifted to the fixed
original source; no independently chosen replacement phase is inserted. -/

universe u v w t
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.ExactEPGeometry.OldGateMaximality
open CCO.ParityHasse.Original CCO.ParityHasse.Relative
open CCO.RigidGroupoid.Geometry
noncomputable section

/-- E4 and the full largest-lift adjunction apply to this SPECIFIED M,
not only to the M selected by an unrelated existential progress proof. -/
theorem specified_current_maximal_gate_original_lift
    (A B : CurrentSource.{u,v,w,t}) (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts) (c : B.source.Atom p p)
    (noOdd : ∀ x : B.Point p, ∀ n : Nat, Odd n →
      ¬relPow (B.source.atomRel c) n x x)
    (M : MaximalGate B.source B.homogeneous
      (evenColourEq B.source B.homogeneous c)
      (connectivityColourEq B.source B.homogeneous c)) :
    ∃ (Yold : ExactEq A.source (P.parent p))
      (Uold : ColourEq A.source (P.parent p)),
      Yold.val = evenColourEq A.source A.homogeneous (P.atom p p c) ∧
      Uold = connectivityColourEq A.source A.homogeneous (P.atom p p c) ∧
      Maximal (OriginalGateCandidate A.source (P.parent p) Yold Uold)
        (PrefixExactLargestLift.largest A B P transport tp p
          (⟨M.kernel,M.maximal.1.1⟩ : ExactEq B.source p)) := by
  let oldc := P.atom p p c
  have atom : OriginalPivotTrace.currentTrace A B P (A.source.atomRel oldc) =
      B.source.atomRel c := by
    funext x y
    exact propext (OldGatePivotBridge.current_parent_atom_iff A B P c x y)
  obtain ⟨x,y,hxy⟩ := B.source.realized c
  have nonempty : TRel.Nonempty
      (OriginalPivotTrace.currentTrace A B P (A.source.atomRel oldc)) := by
    rw [atom]
    exact ⟨x,y,hxy⟩
  have oldNoOdd := OriginalPivotTrace.original_atom_no_odd A B P tp oldc nonempty
    (by simpa only [atom] using noOdd)
  obtain ⟨DY,_,hDY,_⟩ := parity_profiles_nonempty_exact A.source A.homogeneous oldc
  let Yold : ExactEq A.source (P.parent p) :=
    ⟨evenColourEq A.source A.homogeneous oldc,
      ⟨DY,by funext a b; exact propext (hDY a b)⟩⟩
  let Uold := connectivityColourEq A.source A.homogeneous oldc
  have oldCover : Yold.val ⋖ Uold :=
    parity_seed_cover A.source A.homogeneous oldc oldNoOdd
  have currentCover : evenColourEq B.source B.homogeneous c ⋖
      connectivityColourEq B.source B.homogeneous c :=
    parity_seed_cover B.source B.homogeneous c noOdd
  have E4 := OriginalPivotTrace.original_atom_E4 A B P tp oldc nonempty
  have yTrace : evenColourEq B.source B.homogeneous c =
      (PrefixExactRestriction.rho A B P transport p Yold).val := by
    apply ColourEq.ext B.source p
    intro a b
    change EvenWalk (B.source.atomRel c) a b ↔
      (PrefixExactRestriction.rho A B P transport p Yold) a b
    rw [PrefixExactRestriction.rho_iff]
    change EvenWalk (B.source.atomRel c) a b ↔
      (evenColourEq A.source A.homogeneous oldc) (P.point p a) (P.point p b)
    simpa only [atom] using (E4.1 a b).symm
  have uTrace (a b : B.Point p) :
      connectivityColourEq B.source B.homogeneous c a b ↔
        Uold (P.point p a) (P.point p b) := by
    change ConnectedWalk (B.source.atomRel c) a b ↔
      (connectivityColourEq A.source A.homogeneous oldc) (P.point p a) (P.point p b)
    simpa only [atom] using (E4.2.2 a b).symm
  exact ⟨Yold,Uold,rfl,rfl,
    OldGateActualProvider.lift_actual_maximal_gate A B P transport tp p
      Yold Uold _ _ yTrace oldCover uTrace currentCover M⟩

def actualPhasePrefix
    {A : CurrentSource.{u,v,w,t}} (s : CertifiedGateTower.ExactPrefix A)
    {r : s.current.Sorts} {K : Kernel s.current.source r}
    (phase : SourcePhase s.current.source s.current.homogeneous
      (exactCalculus_of_homogeneous_CCO
        s.current.source s.current.homogeneous s.current.cco) K) :
    CertifiedGateTower.ExactPrefix A where
  current := SourceAge.SingleStep.successor s.current phase
  reduct := s.reduct.compose (SourceAge.SingleStep.projection s.current phase)
  transport := ExactTraceTransport.compose _ _ s.transport
    (canonical_step_exact_transport s.current phase)
  product := ExactTraceProduct.compose _ _ s.transport s.product
    (canonical_step_exact_transport s.current phase)
    (canonical_step_exact_product s.current phase)

private theorem actualPhasePrefix_kernel_cast
    {A : CurrentSource.{u,v,w,t}} (s : CertifiedGateTower.ExactPrefix A)
    {r : s.current.Sorts} {K L : Kernel s.current.source r}
    (he : K = L)
    (phase : SourcePhase s.current.source s.current.homogeneous
      (exactCalculus_of_homogeneous_CCO
        s.current.source s.current.homogeneous s.current.cco) K) :
    actualPhasePrefix s (he ▸ phase) = actualPhasePrefix s phase := by
  cases he
  rfl

/-- Any ACTUAL phase has source-certified GateChoice data over its fixed
original exact prefix, with the SAME phase retained through the literal
kernel equality. This discharges the step interface of coded safe history. -/
theorem actual_phase_has_certified_gate_choice
    (A : CurrentSource.{u,v,w,t}) (s : CertifiedGateTower.ExactPrefix A)
    {r : s.current.Sorts} (K : Kernel s.current.source r)
    (phase : SourcePhase s.current.source s.current.homogeneous
      (exactCalculus_of_homogeneous_CCO
        s.current.source s.current.homogeneous s.current.cco) K) :
    ∃ choice : CertifiedGateTower.GateChoice s,
      CertifiedGateTower.successor s choice = actualPhasePrefix s phase := by
  obtain ⟨c,noOdd,_,M,hM⟩ := actualPhaseRoot_maximalGate s.current K phase
  obtain ⟨Yold,Uold,hY,hU,hMax⟩ := specified_current_maximal_gate_original_lift
    A s.current s.reduct s.transport s.product r c noOdd M
  let KM := MaximalGate.kernel s.current.source s.current.homogeneous
    (evenColourEq s.current.source s.current.homogeneous c)
    (connectivityColourEq s.current.source s.current.homogeneous c) M
  have kernelEq : KM = K := by
    apply Kernel.ext_setoid s.current.source
    exact congrArg (fun E : ColourEq s.current.source r => E.val) hM
  let phaseM : SourcePhase s.current.source s.current.homogeneous
      (exactCalculus_of_homogeneous_CCO
        s.current.source s.current.homogeneous s.current.cco) KM := kernelEq.symm ▸ phase
  let choice : CertifiedGateTower.GateChoice s := {
    p := r
    c := c
    Yold := Yold
    Uold := Uold
    M := M
    phase := phaseM
    current_no_odd := noOdd
    old_even := hY
    old_connectivity := hU
    maximal_old := hMax
    decreases := SourceAge.SingleStep.potential_decreases s.current phaseM }
  refine ⟨choice,?_⟩
  change actualPhasePrefix s phaseM = actualPhasePrefix s phase
  exact actualPhasePrefix_kernel_cast s kernelEq.symm phase

end
end CCO.AutomaticEPCore
