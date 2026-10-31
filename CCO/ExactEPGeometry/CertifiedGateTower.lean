import CCO.ExactEPGeometry.OldGateObstructionStep
import CCO.ExactEPGeometry.CanonicalStepProduct
import CCO.APCharacter.Towers.FiniteHistory

/-!
# B062 C28 / C43: certified finite safe tower with original-gate provenance

The generic CurrentSource.ActualStep forgets which current odd orbital
and accepted MaximalGate produced its SourcePhase. Such loss cannot
justify the source's claim about a CANONICAL ORIGINAL old gate in
every stage. We therefore construct a different, richer finite history.

Each state stores the ACTUAL original-to-current unary reduct together
with already PROVED two-way RAW-exactness and full typed nonempty-input
TP certificates. Each step stores ONE real current orbital c,
its actual CCO/no-odd witness, the original even and connectivity
equivalences, a real accepted full MaximalGate M, its greatest ORIGINAL
RAW-exact lift L_p(M.kernel), and the EXACT SourcePhase constructed
from the SAME M. That phase, not an independently selected one, produces
the actual next homogeneous AP+HOM CCO source and a strict rank drop.

The successor reduct and exact/TP certificates are composed from
the genuine SourceAge.SingleStep and C28, not postulated for an
arbitrary unary refinement. Finite rank induction then gives a
terminating ACTUAL gate-certified safe tower, including the zero-step
case. No original/quotient SAP, arbitrary quotient section or new axiom.
-/

universe u v w t

namespace CCO.ExactEPGeometry.CertifiedGateTower

open APCharacter APCharacter.Towers
open CCO.ExactEPGeometry
open CCO.ExactEPGeometry.OldGateMaximality
open CCO.ExactEPGeometry.OldGateObstructionStep
open CCO.ParityHasse.Original
open CCO.ParityHasse.Relative
open CCO.RigidGroupoid.Geometry

noncomputable section

/-- A real prefix of one FIXED original AP+HOM CCO source, with an
actual whole-carrier reduct and BOTH proved RAW exact and typed (TP)
certificates. No theorem about an arbitrary unary refinement is
stored as a free field: the constructors below supply each certificate. -/
structure ExactPrefix (original : CurrentSource.{u,v,w,t}) where
  current : CurrentSource.{u,v,w,t}
  reduct : UnaryReduct original.source current.source
  transport : ExactTraceTransport original.source current.source reduct
  product : ExactTraceProduct original.source current.source reduct

/-- The honest zero-stage prefix uses literal identity and the real
identity exact/TP proofs. -/
def initial (original : CurrentSource.{u,v,w,t}) : ExactPrefix original where
  current := original
  reduct := UnaryReduct.identity original.source
  transport := ExactTraceTransport.identity original.source
  product := ExactTraceProduct.identity original.source

/-- A chosen real old-gate step contains ALL data discarded by the
generic phase-only SourceAge.SingleStep and the true strict potential
decrease. The named old gate is the maximal ORIGINAL full RAW-exact
fiber lift, not a separately selected or hypothesized predecessor. -/
structure GateChoice
    {original : CurrentSource.{u,v,w,t}}
    (s : ExactPrefix original) where
  p : s.current.Sorts
  c : s.current.source.Atom p p
  Yold : ExactEq original.source (s.reduct.parent p)
  Uold : ColourEq original.source (s.reduct.parent p)
  M : MaximalGate s.current.source s.current.homogeneous
    (evenColourEq s.current.source s.current.homogeneous c)
    (connectivityColourEq s.current.source s.current.homogeneous c)
  phase : SourcePhase s.current.source s.current.homogeneous
    (exactCalculus_of_homogeneous_CCO
      s.current.source s.current.homogeneous s.current.cco)
    (APCharacter.MaximalGate.kernel s.current.source s.current.homogeneous
      (evenColourEq s.current.source s.current.homogeneous c)
      (connectivityColourEq s.current.source s.current.homogeneous c) M)
  current_no_odd : ∀ x : s.current.Point p, ∀ n : Nat, Odd n →
    ¬relPow (s.current.source.atomRel c) n x x
  old_even : Yold.val = evenColourEq original.source original.homogeneous
    (s.reduct.atom p p c)
  old_connectivity : Uold =
    connectivityColourEq original.source original.homogeneous
      (s.reduct.atom p p c)
  maximal_old : Maximal
    (OriginalGateCandidate original.source (s.reduct.parent p) Yold Uold)
    (PrefixExactLargestLift.largest
      original s.current s.reduct s.transport s.product p
      (⟨M.kernel,M.maximal.1.1⟩ : ExactEq s.current.source p))
  decreases : (SourceAge.SingleStep.successor s.current phase).potential <
    s.current.potential

/-- The ACTUAL next source and its exact original reduct are built
from the SAME GateChoice phase, not selected by an independent
existential elimination. C28 discharges both compositional proofs. -/
def successor
    {original : CurrentSource.{u,v,w,t}}
    (s : ExactPrefix original) (choice : GateChoice s) :
    ExactPrefix original := by
  let T := SourceAge.SingleStep.successor s.current choice.phase
  let Q := SourceAge.SingleStep.projection s.current choice.phase
  let ht : ExactTraceTransport s.current.source T.source Q :=
    canonical_step_exact_transport s.current choice.phase
  let hp : ExactTraceProduct s.current.source T.source Q :=
    canonical_step_exact_product s.current choice.phase
  exact {
    current := T
    reduct := s.reduct.compose Q
    transport := ExactTraceTransport.compose s.reduct Q s.transport ht
    product := ExactTraceProduct.compose
      s.reduct Q s.transport s.product ht hp
  }

/-- An actual certified character step literally includes the choice
of its current pivot, original gate and phase. This is stronger than
the generic ActualStep relation used by the earlier C28 interface. -/
def Step {original : CurrentSource.{u,v,w,t}}
    (s t : ExactPrefix original) : Prop :=
  ∃ choice : GateChoice s, t = successor s choice

/-- Every ACTUAL finite-index obstruction admits an actual
full-character successor whose same selected M certifies a maximal
ORIGINAL exact gate, and whose global original reduct, exactness
and (TP) have all been constructed. -/
theorem progress
    {original : CurrentSource.{u,v,w,t}}
    (s : ExactPrefix original)
    (h : s.current.Obstruction) :
    ∃ t : ExactPrefix original, Step s t := by
  obtain ⟨p,c,Yold,Uold,M,phase,hOdd,hY,hU,hMax,hDec⟩ :=
    obstruction_produces_certified_old_gate
      original s.current s.reduct s.transport s.product h
  let choice : GateChoice s :=
    { p := p
      c := c
      Yold := Yold
      Uold := Uold
      M := M
      phase := phase
      current_no_odd := hOdd
      old_even := hY
      old_connectivity := hU
      maximal_old := hMax
      decreases := hDec }
  exact ⟨successor s choice,choice,rfl⟩

/-- The integer potential actually drops at EVERY source-certified
old-gate step, rather than just after an unnamed hypothetical split. -/
theorem decreases
    {original : CurrentSource.{u,v,w,t}}
    {s t : ExactPrefix original} (step : Step s t) :
    t.current.potential < s.current.potential := by
  obtain ⟨choice,rfl⟩ := step
  exact choice.decreases

/-- A real terminal CURRENT AP+HOM CCO source is reached after at most
the original finite potential many chosen, source-certified steps. The
history RETAINS the old orbital and ORIGINAL maximal gate at each step,
while the terminal prefix carries its genuine global original reduct
and compiled two-way exact/TP theorems.

In particular this is not the earlier history of arbitrary unnamed
ActualSteps: its step predicate keeps original-gate provenance. -/
theorem terminalisation
    (original : CurrentSource.{u,v,w,t}) :
    ∃ terminal : ExactPrefix original,
      ∃ history : History Step (initial original) terminal,
        ¬terminal.current.Obstruction ∧
          history.length + terminal.current.potential ≤ original.potential ∧
          ExactTraceTransport original.source terminal.current.source
            terminal.reduct ∧
          ExactTraceProduct original.source terminal.current.source
            terminal.reduct := by
  obtain ⟨terminal,h,ht,hbound⟩ :=
    eliminate_obstructions Step
      (fun s : ExactPrefix original => s.current.potential)
      (fun s : ExactPrefix original => s.current.Obstruction)
      (fun s hs => progress s hs)
      (fun {_ _} step => decreases step) (initial original)
  exact ⟨terminal,h,ht,hbound,terminal.transport,terminal.product⟩

end
end CCO.ExactEPGeometry.CertifiedGateTower
