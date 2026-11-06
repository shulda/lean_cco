import CCO.ExactEPGeometry.NamedCurrentSourceIso
import CCO.ExactEPGeometry.OriginalRetainedSelectedSourceIso
import CCO.ExactEPGeometry.OriginalRetainedActualSelectedGate
import CCO.ExactEPGeometry.OriginalDiscardedSelectedSourceIso
import CCO.ExactEPGeometry.CertifiedOriginalKernel

/-!
# B062 C103: erase exactly the discarded stages of an actual source tower

States are complete named-source isomorphism classes. Every retained edge
is the class of a genuine full SourcePhase successor, with an actual maximal
full-exact complement and reachable parity pivot. Every discarded edge is
identified by its genuine whole source isomorphism. Thus induction removes
discarded edges literally, rather than retaining formal zero-cost steps.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open Classical
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original CCO.ParityHasse.Relative
noncomputable section

/-- A genuine maximal full-character successor, up to complete named-source
isomorphism. The parity pivot and full maximal gate are actual witnesses. -/
def SafeSourceStep (a b : NamedSourceClass.{u,v,w,t}) : Prop :=
  ∃ (B : CurrentSource.{u,v,w,t}) (r : B.Sorts) (K : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) K),
    namedSourceClass B = a ∧ namedSourceClass (SingleStep.successor B phase) = b ∧
    ∃ c : B.source.Atom r r,
      (∀ x : B.Point r, ∀ n : Nat, Odd n → ¬relPow (B.source.atomRel c) n x x) ∧
      (∀ x : B.Point r,
        relativeIndex (evenColourEq B.source B.homogeneous c).val
          (connectivityColourEq B.source B.homogeneous c).val x = 2) ∧
      ∃ M : MaximalGate B.source B.homogeneous
        (evenColourEq B.source B.homogeneous c)
        (connectivityColourEq B.source B.homogeneous c),
        M.kernel = (current_kernel_exact_eq B K).val

/-- The actual occupancy-selected original E-quotient at an arbitrary
certified prefix, with all its source providers already discharged. -/
def quotient (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) (s : CertifiedGateTower.ExactPrefix A) :
    CurrentSource.{u,v,v,t} :=
  originalExactSelectedQuotientCurrentSource
    A s.current s.reduct s.transport base hOne E

/-- Any genuinely retained edge is a whole actual maximal-character step
on the earlier selected quotient, with its corrected complete character. -/
theorem originalQuotient_retainedStep
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step) :
    SafeSourceStep (namedSourceClass (quotient A base hOne E s))
      (namedSourceClass (quotient A base hOne E next)) := by
  let choice : CertifiedGateTower.GateChoice s := Classical.choose step
  have hNext : next = CertifiedGateTower.successor s choice := Classical.choose_spec step
  rw [hNext]
  let hBase : base = s.reduct.parent choice.p := hOne _
  let Eold := oldExactEqCast A.source hBase.symm E
  let K := MaximalGate.kernel s.current.source s.current.homogeneous
    (evenColourEq s.current.source s.current.homogeneous choice.c)
    (connectivityColourEq s.current.source s.current.homogeneous choice.c) choice.M
  let Gate := PrefixExactLargestLift.largest A s.current s.reduct s.transport
    s.product choice.p (current_kernel_exact_eq s.current K)
  have hCast : E ≤ oldExactEqCast A.source hBase Gate := hE
  have hEold : Eold ≤ Gate := by
    have h := oldExactEqCast_mono A.source hBase.symm E
      (oldExactEqCast A.source hBase Gate) hCast
    simpa only [oldExactEqCast_cancel] using h
  have one : ∀ i j : A.Sorts, i = j := fun i j => (hOne i).symm.trans (hOne j)
  have hb := hBase
  cases hb
  let QB := quotient A (s.reduct.parent choice.p) hOne E s
  let KQ := originalRetainedSelectedKernel A s.current s.reduct s.transport
    s.product one K E hEold (Reached.root K)
  let phaseQ := originalRetainedActualSelectedPhase A s.current s.reduct s.transport
    s.product one K choice.phase E hEold
  let QN := quotient A (s.reduct.parent choice.p) hOne E (CertifiedGateTower.successor s choice)
  let M := SingleStep.successor QB phaseQ
  let iso : NamedCurrentSourceIso QN M := {
    sorts := originalRetainedOccupancyChildEquiv A s.current s.reduct s.transport
      s.product one K choice.phase E hEold
    points := originalRetainedSelectedPointEquiv A s.current s.reduct s.transport
      s.product one K choice.phase E hEold
    owner := originalRetainedSelectedPointEquiv_owner A s.current s.reduct s.transport
      s.product one K choice.phase E hEold
    palette := originalRetainedSelectedPointEquiv_palette A s.current s.reduct s.transport
      s.product one K choice.phase E hEold }
  refine ⟨QB,Quotient.mk'' choice.p,KQ,phaseQ,rfl,(namedSourceClass_eq iso).symm,?_⟩
  exact actualPhaseRoot_maximalGate QB KQ phaseQ

/-- A genuinely discarded edge is the SAME complete source isomorphism
class, including every unary occupancy name and every mixed pair colour. -/
theorem originalQuotient_discardedStep
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : ¬ E ≤ certifiedStepOriginalGate A base hOne step) :
    namedSourceClass (quotient A base hOne E s) =
      namedSourceClass (quotient A base hOne E next) := by
  let choice : CertifiedGateTower.GateChoice s := Classical.choose step
  have hNext : next = CertifiedGateTower.successor s choice := Classical.choose_spec step
  rw [hNext]
  let hBase : base = s.reduct.parent choice.p := hOne _
  let Eold := oldExactEqCast A.source hBase.symm E
  let K := MaximalGate.kernel s.current.source s.current.homogeneous
    (evenColourEq s.current.source s.current.homogeneous choice.c)
    (connectivityColourEq s.current.source s.current.homogeneous choice.c) choice.M
  let Gate := PrefixExactLargestLift.largest A s.current s.reduct s.transport
    s.product choice.p (current_kernel_exact_eq s.current K)
  have hNot : ¬ Eold ≤ Gate := by
    intro h
    apply hE
    change E ≤ oldExactEqCast A.source hBase Gate
    have hc := oldExactEqCast_mono A.source hBase Eold Gate h
    simpa only [Eold,oldExactEqCast_cancel] using hc
  have one : ∀ i j : A.Sorts, i = j := fun i j => (hOne i).symm.trans (hOne j)
  have hb := hBase
  cases hb
  let QB := quotient A (s.reduct.parent choice.p) hOne E s
  let QN := quotient A (s.reduct.parent choice.p) hOne E (CertifiedGateTower.successor s choice)
  let iso : NamedCurrentSourceIso QN QB := {
    sorts := originalDiscardedOccupancySortClassEquiv A s.current s.reduct s.transport
      s.product one K choice.phase E hNot
    points := originalPhaseSelectedPointEquiv A s.current s.reduct s.transport
      K choice.phase (s.reduct.parent choice.p) hOne E
    owner := originalDiscardedSelectedPointEquiv_owner A s.current s.reduct s.transport
      s.product one K choice.phase E hNot
    palette := fun q z q' z' => originalDiscardedSelectedTaggedColour_iff
      A s.current s.reduct s.transport s.product one K choice.phase E hNot q' z' q z }
  exact (namedSourceClass_eq iso).symm

/-- The WHOLE quotient safe tower of ANY supplied actual certified history.
Its real number of safe stages is exactly the number of original selected
gates containing E. Every other original step has literally been erased by
the proved complete source isomorphism, including a zero-stage history. -/
theorem originalQuotientSafeHistory
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {s terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s terminal) :
    ∃ projected : History SafeSourceStep
        (namedSourceClass (quotient A base hOne E s))
        (namedSourceClass (quotient A base hOne E terminal)),
      projected.length = (certifiedHistoryOriginalGates A base hOne history).countP
        (fun G => decide (E ≤ G)) := by
  classical
  induction history with
  | nil s => exact ⟨.nil _,rfl⟩
  | cons step tail ih =>
    obtain ⟨projected,hLength⟩ := ih
    by_cases hE : E ≤ certifiedStepOriginalGate A base hOne step
    · refine ⟨.cons (originalQuotient_retainedStep A base hOne E step hE) projected,?_⟩
      simp [History.length,certifiedHistoryOriginalGates,hE,hLength]
    · have hEq := originalQuotient_discardedStep A base hOne E step hE
      rw [hEq]
      refine ⟨projected,?_⟩
      simpa [certifiedHistoryOriginalGates,hE] using hLength

end
end CCO.ExactEPGeometry
