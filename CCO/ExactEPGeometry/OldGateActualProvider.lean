import CCO.ExactEPGeometry.OldGateMaximality

/-!
# B062 C43: consume a genuine accepted current MaximalGate certificate

The preceding `OldGateMaximality.lift_maximal_gate` proves the exact
order-theoretic transfer. Here the current gate is not an abstract
assumed maximal predicate: it is the REAL provider's
`ParityHasse.Relative.MaximalGate`, whose maximality quantifies over
every current full-RAW-exact invariant equivalence.

The geometric identification of the actual current parity endpoints
with the original even/connectivity traces is kept explicit; source E4
provides it when the real selected pivot is available. The current
parity cover and actual gate provider are not replaced by a new axiom.
-/

universe u v w t

namespace CCO.ExactEPGeometry.OldGateActualProvider

open APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ExactEPGeometry.PrefixExactRestriction
open CCO.ExactEPGeometry.PrefixExactLargestLift
open CCO.ExactEPGeometry.OldGateMaximality
open CCO.ParityHasse.Original
open CCO.ParityHasse.Relative

noncomputable section

/-- A GENUINELY constructed current maximal gate from the accepted
provider, with the old/source parity-interval relation identities of
E4, has a maximal ORIGINAL RAW-exact lift. The actual original upper U
does not need to be exact, and the current gate ranges over all exact
invariant current relations rather than just one selected presentation. -/
theorem lift_actual_maximal_gate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (p : B.Sorts)
    (Y : ExactEq A.source (P.parent p))
    (Uold : ColourEq A.source (P.parent p))
    (Ycur Ucur : ColourEq B.source p)
    (hYcur : Ycur = (rho A B P transport p Y).val)
    (hCover : Y.val ⋖ Uold)
    (hUtrace : ∀ x y : B.Point p,
      Ucur x y ↔ Uold (P.point p x) (P.point p y))
    (hCurrentCover : Ycur ⋖ Ucur)
    (M : MaximalGate B.source B.homogeneous Ycur Ucur) :
    let K : ExactEq B.source p := ⟨M.kernel,M.maximal.1.1⟩
    Maximal (OriginalGateCandidate A.source (P.parent p) Y Uold)
      (largest A B P transport tp p K) := by
  dsimp only
  let K : ExactEq B.source p := ⟨M.kernel,M.maximal.1.1⟩
  have hStrict : ¬ Ucur ≤ (rho A B P transport p Y).val := by
    rw [←hYcur]
    exact hCurrentCover.1.not_ge
  have hMax : Maximal
      (CurrentGateCandidate A B P transport p Y Ucur) K := by
    constructor
    · constructor
      · change (rho A B P transport p Y).val ≤ M.kernel
        rw [←hYcur]
        exact M.maximal.1.2.1
      · change M.kernel ⊓ Ucur = (rho A B P transport p Y).val
        rw [←hYcur]
        exact M.maximal.1.2.2
    · intro Z hZ hKZ
      have hCandidate : Candidate B.source Ycur Ucur Z.val := by
        refine ⟨Z.property, ?_, ?_⟩
        · have h : rho A B P transport p Y ≤ Z := hZ.1
          change (rho A B P transport p Y).val ≤ Z.val at h
          rw [←hYcur] at h
          exact h
        · have h : Z.val ⊓ Ucur = (rho A B P transport p Y).val :=
            hZ.2
          rw [←hYcur] at h
          exact h
      exact M.maximal.2 hCandidate hKZ
  exact lift_maximal_gate A B P transport tp p Y Uold Ucur
    hCover hUtrace hStrict K hMax

end
end CCO.ExactEPGeometry.OldGateActualProvider
