import CCO.ExactEPGeometry.OldGatePivotBridge
import CCO.APCharacter.SourceAge.SingleStep
import CCO.ParityHasse.Original.SourceHasse

/-!
# B062 C38–C43: residual obstruction selects a real original gate step

The actual CURRENT finite-index obstruction has an original current
diversity atom in the strict interval. The accepted AP+HOM CCO parity
provider proves that specific atom has no odd closed walk, rather
than asking the B062 consumer to supply a no-odd-walk predicate.

The selected orbital feeds the SAME full current MaximalGate whose
original largest exact lift and next genuine SourcePhase are constructed
together by OldGatePivotBridge. The successor's potential strictly
decreases, and the resulting step is the real AP-only
SourceAge.SingleStep.actualStep, not an arbitrary nominal refinement.

The certificate retains the atom, BOTH original parity equivalences,
the original maximal exact gate, and the actual phase associated with
the selected MaximalGate. It does not claim that an independent
previously selected SourcePhase stores those certificates.
-/

universe u v w t

namespace CCO.ExactEPGeometry.OldGateObstructionStep

open APCharacter APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ExactEPGeometry.OldGateMaximality
open CCO.ParityHasse.Original
open CCO.ParityHasse.Relative
open CCO.RigidGroupoid.Geometry

noncomputable section

/-- C38 input is obtained from an ACTUAL current obstruction. The
chosen current atom lies in the strict full invariant interval,
and the NO-ODD source theorem is supplied by actual original AP+CCO
and finite relative index. No graph-bipartiteness assumption appears. -/
theorem obstruction_has_actual_bipartite_pivot
    (B : CurrentSource.{u,v,w,t}) (h : B.Obstruction) :
    ∃ (p : B.Sorts) (c : B.source.Atom p p),
      ∀ x : B.Point p, ∀ n : Nat, Odd n →
        ¬relPow (B.source.atomRel c) n x x := by
  obtain ⟨p,E,F,a,hEF,hFin⟩ := h
  letI : Finite (RelativeClass E.val F.val a) := hFin
  obtain ⟨c,hc⟩ := exists_atom_difference B.source E F hEF
  have hCCO : SemanticCCO.{u,v,0,w} B.source :=
    semanticCCO_change_universe B.source B.cco
  have hWalk := no_odd_orbital_walk B.source B.homogeneous
    hCCO E F a c hc
  refine ⟨p,c,?_⟩
  intro x n hn hp
  obtain ⟨q,hq⟩ := (relPow_atom_iff_walk B.source c n x x).mp hp
  exact hWalk x q (by simpa only [hq] using hn)

/-- A *real* full-character step certificate with its chosen original
old gate. The phase and the ORIGINAL maximal lift come from the very
same actual current MaximalGate, preserving its full upstream origin.

The terminal safe tower will be built from these certified steps:
generic CurrentSource.ActualStep does not retain the provenance. -/
def CertifiedOldGateStep
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P) : Prop :=
  ∃ (p : B.Sorts) (c : B.source.Atom p p)
    (Yold : ExactEq A.source (P.parent p))
    (Uold : ColourEq A.source (P.parent p))
    (M : MaximalGate B.source B.homogeneous
      (evenColourEq B.source B.homogeneous c)
      (connectivityColourEq B.source B.homogeneous c))
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco)
      (APCharacter.MaximalGate.kernel B.source B.homogeneous
        (evenColourEq B.source B.homogeneous c)
        (connectivityColourEq B.source B.homogeneous c) M)),
      (∀ x : B.Point p, ∀ n : Nat, Odd n →
        ¬relPow (B.source.atomRel c) n x x) ∧
      Yold.val =
        evenColourEq A.source A.homogeneous (P.atom p p c) ∧
      Uold =
        connectivityColourEq A.source A.homogeneous (P.atom p p c) ∧
      Maximal (OriginalGateCandidate A.source (P.parent p)
        Yold Uold)
        (PrefixExactLargestLift.largest A B P transport tp p
          (⟨M.kernel,M.maximal.1.1⟩ : ExactEq B.source p)) ∧
      (SourceAge.SingleStep.successor B phase).potential < B.potential

/-- ACTUAL source-strength construction: any remaining finite-index
current obstruction yields the next strict-rank full-character step,
with a chosen ORIGINAL maximal exact gate proved from that very same
current pivot and the identical current MaximalGate M. -/
theorem obstruction_produces_certified_old_gate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (h : B.Obstruction) :
    CertifiedOldGateStep A B P transport tp := by
  obtain ⟨p,c,hNoOdd⟩ := obstruction_has_actual_bipartite_pivot B h
  obtain ⟨Yold,Uold,M,hY,hU,hMax,hPhase⟩ :=
    OldGatePivotBridge.actual_pivot_and_selected_gate
      A B P transport tp p c hNoOdd
  obtain ⟨phase⟩ := hPhase
  exact ⟨p,c,Yold,Uold,M,phase,hNoOdd,hY,hU,hMax,
    SourceAge.SingleStep.potential_decreases B phase⟩

end
end CCO.ExactEPGeometry.OldGateObstructionStep
