import CCO.ExactEPGeometry.OriginalQuotientRootPredicates
import CCO.ExactEPGeometry.OriginalQuotientSafeHistory

/-! The whole safe history RELATIVE TO the fixed original E-quotient
binary predicates.  Each code coordinate is the literal predicate E;a;E
for a specified original atom (including equality), with its original name.
Neither discarded nor retained isomorphisms may rename this code. -/

universe u v w t
namespace CCO.ExactEPGeometry
open Classical APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original CCO.ParityHasse.Relative
noncomputable section

/-- Actual selected prefix carrying the SAME fixed original quotient
predicate family, not only an unlabeled current orbital partition. -/
def originalCodedQuotient (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base) (s : CertifiedGateTower.ExactPrefix A) :
    CodedCurrentSource.{u,v,v,t} (Age.Colour A.source → Prop) where
  current := quotient A base hOne E s
  code := originalQuotientRootCode A s.current s.reduct s.transport base hOne E

/-- Any genuinely retained edge is a whole actual maximal-character step
on the earlier selected quotient, with its corrected complete character. -/
theorem originalCodedQuotient_retainedStep
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step) :
    CodedSafeSourceStep (codedSourceClass (originalCodedQuotient A base hOne E s))
      (codedSourceClass (originalCodedQuotient A base hOne E next)) := by
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
  let QB := originalCodedQuotient A (s.reduct.parent choice.p) hOne E s
  let KQ := originalRetainedSelectedKernel A s.current s.reduct s.transport
    s.product one K E hEold (Reached.root K)
  let phaseQ := originalRetainedActualSelectedPhase A s.current s.reduct s.transport
    s.product one K choice.phase E hEold
  let QN := originalCodedQuotient A (s.reduct.parent choice.p) hOne E (CertifiedGateTower.successor s choice)
  let M := QB.successor phaseQ
  let iso : CodedCurrentSourceIso QN M := {
    toNamedCurrentSourceIso := {
    sorts := originalRetainedOccupancyChildEquiv A s.current s.reduct s.transport
      s.product one K choice.phase E hEold
    points := originalRetainedSelectedPointEquiv A s.current s.reduct s.transport
      s.product one K choice.phase E hEold
    owner := originalRetainedSelectedPointEquiv_owner A s.current s.reduct s.transport
      s.product one K choice.phase E hEold
    palette := originalRetainedSelectedPointEquiv_palette A s.current s.reduct s.transport
      s.product one K choice.phase E hEold }
    code_eq := originalRetainedSelectedPointEquiv_rootCode A s.current s.reduct s.transport
      s.product one K choice.phase E hEold }
  refine ⟨QB,Quotient.mk'' choice.p,KQ,phaseQ,rfl,(codedSourceClass_eq iso).symm,?_⟩
  exact actualPhaseRoot_maximalGate QB.current KQ phaseQ

/-- A genuinely discarded edge is the SAME complete source isomorphism
class, including every unary occupancy name and every mixed pair colour. -/
theorem originalCodedQuotient_discardedStep
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : ¬ E ≤ certifiedStepOriginalGate A base hOne step) :
    codedSourceClass (originalCodedQuotient A base hOne E s) =
      codedSourceClass (originalCodedQuotient A base hOne E next) := by
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
  let QB := originalCodedQuotient A (s.reduct.parent choice.p) hOne E s
  let QN := originalCodedQuotient A (s.reduct.parent choice.p) hOne E (CertifiedGateTower.successor s choice)
  let iso : CodedCurrentSourceIso QN QB := {
    toNamedCurrentSourceIso := {
    sorts := originalDiscardedOccupancySortClassEquiv A s.current s.reduct s.transport
      s.product one K choice.phase E hNot
    points := originalPhaseSelectedPointEquiv A s.current s.reduct s.transport
      K choice.phase (s.reduct.parent choice.p) hOne E
    owner := originalDiscardedSelectedPointEquiv_owner A s.current s.reduct s.transport
      s.product one K choice.phase E hNot
    palette := fun q z q' z' => originalDiscardedSelectedTaggedColour_iff
      A s.current s.reduct s.transport s.product one K choice.phase E hNot q' z' q z }
    code_eq := originalPhaseSelectedPointEquiv_rootCode A s.current s.reduct s.transport
      (s.reduct.parent choice.p) hOne E K choice.phase }
  exact (codedSourceClass_eq iso).symm

/-- The WHOLE quotient safe tower of ANY supplied actual certified history.
Its real number of safe stages is exactly the number of original selected
gates containing E. Every other original step has literally been erased by
the proved complete source isomorphism, including a zero-stage history. -/
theorem originalCodedQuotientSafeHistory
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {s terminal : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s terminal) :
    ∃ projected : History CodedSafeSourceStep
        (codedSourceClass (originalCodedQuotient A base hOne E s))
        (codedSourceClass (originalCodedQuotient A base hOne E terminal)),
      projected.length = (certifiedHistoryOriginalGates A base hOne history).countP
        (fun G => decide (E ≤ G)) := by
  classical
  induction history with
  | nil s => exact ⟨.nil _,rfl⟩
  | cons step tail ih =>
    obtain ⟨projected,hLength⟩ := ih
    by_cases hE : E ≤ certifiedStepOriginalGate A base hOne step
    · refine ⟨.cons (originalCodedQuotient_retainedStep A base hOne E step hE) projected,?_⟩
      simp [History.length,certifiedHistoryOriginalGates,hE,hLength]
    · have hEq := originalCodedQuotient_discardedStep A base hOne E step hE
      rw [hEq]
      refine ⟨projected,?_⟩
      simpa [certifiedHistoryOriginalGates,hE] using hLength

end
end CCO.ExactEPGeometry
