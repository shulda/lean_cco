import CCO.ExactEPGeometry.OriginalCodedQuotientSafeHistory

/-!
# The quotient history with its original stage and gate provenance

The endpoint-class existence theorem forgets which witnesses produced its
edges. Here a retained edge uses the literal kernel and corrected phase of
the SAME chosen original step. Its certificate includes the actual full
source isomorphism, exact original G/E, its current trace and its universal
largest-lift property. The inductive trace keeps every original intermediate
prefix, in order, including the isomorphism at each discarded stage.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open Classical APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original CCO.ParityHasse.Relative
noncomputable section

namespace QuotientHistoryProvenance

variable (A : CurrentSource.{u,v,w,t})
variable (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
variable (E : ExactEq A.source base)

abbrev Choice {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) := Classical.choose step

def oldKernel {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) :
    Kernel s.current.source (Choice A step).p :=
  MaximalGate.kernel s.current.source s.current.homogeneous
    (evenColourEq s.current.source s.current.homogeneous (Choice A step).c)
    (connectivityColourEq s.current.source s.current.homogeneous (Choice A step).c)
    (Choice A step).M

def rootE {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) :
    ExactEq A.source (s.reduct.parent (Choice A step).p) :=
  oldExactEqCast A.source (hOne _).symm E

theorem rootE_below {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step) :
    rootE A base hOne E step ≤ PrefixExactLargestLift.largest A s.current
      s.reduct s.transport s.product (Choice A step).p
      (current_kernel_exact_eq s.current (oldKernel A step)) := by
  have h := oldExactEqCast_mono A.source
    (hOne (s.reduct.parent (Choice A step).p)).symm E
    (certifiedStepOriginalGate A base hOne step) hE
  simpa only [certifiedStepOriginalGate, oldExactEqCast_cancel, rootE, Choice,
    oldKernel, current_kernel_exact_eq, APCharacter.MaximalGate.kernel] using h

/-- The literal projected kernel of the SAME old maximal gate. -/
def kernel {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step) :
    Kernel (originalCodedQuotient A base hOne E s).current.source
      (Quotient.mk'' (Choice A step).p) := by
  have hb : base = s.reduct.parent (Choice A step).p := hOne _
  cases hb
  exact originalRetainedSelectedKernel A s.current s.reduct s.transport
    s.product (fun i j => (hOne i).symm.trans (hOne j))
    (oldKernel A step) E (rootE_below A _ hOne E step hE)
    (Reached.root (oldKernel A step))

/-- The prescribed corrected WHOLE character, with no new phase choice. -/
def phase {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step) :
    SourcePhase (originalCodedQuotient A base hOne E s).current.source
      (originalCodedQuotient A base hOne E s).current.homogeneous
      (exactCalculus_of_homogeneous_CCO
        (originalCodedQuotient A base hOne E s).current.source
        (originalCodedQuotient A base hOne E s).current.homogeneous
        (originalCodedQuotient A base hOne E s).current.cco)
      (kernel A base hOne E step hE) := by
  have hb : base = s.reduct.parent (Choice A step).p := hOne _
  cases hb
  exact originalRetainedActualSelectedPhase A s.current s.reduct s.transport
    s.product (fun i j => (hOne i).symm.trans (hOne j))
    (oldKernel A step) (Choice A step).phase E (rootE_below A _ hOne E step hE)

/-- The canonical old gate is the ACTUAL G_i/E, not just some full gate
of an endpoint-equivalent safe step. This records full RAW exactness,
the precise current trace, and largest lift against EVERY full exact gate
on the original quotient, using only this earlier original prefix. -/
def CanonicalOldGate {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) : Prop :=
  let p := (Choice A step).p
  let b := s.reduct.parent p
  let hb : ∀ i : A.Sorts, b = i := fun i => (hOne b).symm.trans (hOne i)
  let e := rootE A base hOne E step
  let J := originalExactSourceKernelFamily A b hb e
  let W := originalExactSourceKernelWords A b hb e
  let hW := originalExactSourceKernelWords_relation A b hb e
  let Q0 := CCO.ExactCRT.CanonicalTyped.source A.source A.homogeneous J W hW
  let pi : A.Point b → Quotient (J b) := CCO.ExactCRT.CanonicalTyped.projection J b
  let G := PrefixExactLargestLift.largest A s.current s.reduct s.transport
    s.product p (current_kernel_exact_eq s.current (oldKernel A step))
  FullExact Q0 (CCO.ExactCRT.quotientRelation pi pi (fun a z => G a z)) ∧
    (∀ x y : s.current.Point p,
      CCO.ExactCRT.quotientRelation pi pi (fun a z => G a z)
        (pi (s.reduct.point p x)) (pi (s.reduct.point p y)) ↔
        (oldKernel A step).rel x y) ∧
    ∀ Z : Kernel Q0 b,
      (∀ x y : s.current.Point p,
        Z.rel (pi (s.reduct.point p x)) (pi (s.reduct.point p y)) →
          (oldKernel A step).rel x y) →
      ∀ q z : Quotient (J b), Z.rel q z →
        CCO.ExactCRT.quotientRelation pi pi (fun a z => G a z) q z

/-- The G in the certificate is literally the selected ORIGINAL gate
stored at this original index, transported only by the named sort equality. -/
theorem originalGate_eq {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) :
    certifiedStepOriginalGate A base hOne step =
      oldExactEqCast A.source (hOne (s.reduct.parent (Choice A step).p))
        (PrefixExactLargestLift.largest A s.current s.reduct s.transport
          s.product (Choice A step).p
          (current_kernel_exact_eq s.current (oldKernel A step))) := rfl

theorem canonicalOldGate {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step) :
    CanonicalOldGate A base hOne E step :=
  originalOneSortLargestQuotientGate_complete A s.current s.reduct s.transport
    s.product (fun i j => (hOne i).symm.trans (hOne j))
    (Choice A step).p (oldKernel A step) (rootE A base hOne E step)
    (rootE_below A base hOne E step hE)

/-- A receiving certificate for ONE retained original edge. Its source,
root, kernel and corrected phase are fixed expressions from that edge.
The actual full marked-age isomorphism fixes every original predicate. -/
structure Retained {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step) where
  iso : CodedCurrentSourceIso
    (originalCodedQuotient A base hOne E next)
    ((originalCodedQuotient A base hOne E s).successor
      (phase A base hOne E step hE))
  root_pullback : originalExactSelectedAtParentKernelPullback A s.current
    s.reduct s.transport base hOne E (kernel A base hOne E step hE) = oldKernel A step
  canonical : CanonicalOldGate A base hOne E step

theorem retained {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next)
    (hE : E ≤ certifiedStepOriginalGate A base hOne step) :
    Nonempty (Retained A base hOne E step hE) := by
  refine ⟨{ iso := ?_
            root_pullback := ?_
            canonical := canonicalOldGate A base hOne E step hE }⟩
  · conv_lhs => rw [certifiedStep_witness_is_actual_successor step]
    have hb : base = s.reduct.parent (Choice A step).p := hOne _
    cases hb
    let one : ∀ i j : A.Sorts, i = j := fun i j => (hOne i).symm.trans (hOne j)
    let hNested := rootE_below A _ hOne E step hE
    exact {
      toNamedCurrentSourceIso := {
        sorts := originalRetainedOccupancyChildEquiv A s.current s.reduct s.transport
          s.product one (oldKernel A step) (Choice A step).phase E hNested
        points := originalRetainedSelectedPointEquiv A s.current s.reduct s.transport
          s.product one (oldKernel A step) (Choice A step).phase E hNested
        owner := originalRetainedSelectedPointEquiv_owner A s.current s.reduct s.transport
          s.product one (oldKernel A step) (Choice A step).phase E hNested
        palette := originalRetainedSelectedPointEquiv_palette A s.current s.reduct s.transport
          s.product one (oldKernel A step) (Choice A step).phase E hNested }
      code_eq := originalRetainedSelectedPointEquiv_rootCode A s.current s.reduct s.transport
        s.product one (oldKernel A step) (Choice A step).phase E hNested }
  · have hb : base = s.reduct.parent (Choice A step).p := hOne _
    cases hb
    let one : ∀ i j : A.Sorts, i = j := fun i j => (hOne i).symm.trans (hOne j)
    let hNested := rootE_below A _ hOne E step hE
    exact originalRetainedActualSelectedGate_rootPullback A s.current s.reduct
      s.transport s.product one (oldKernel A step) E hNested

theorem Retained.toStep {s next : CertifiedGateTower.ExactPrefix A}
    {step : CertifiedGateTower.Step s next}
    {hE : E ≤ certifiedStepOriginalGate A base hOne step}
    (R : Retained A base hOne E step hE) :
    CodedSafeSourceStep (codedSourceClass (originalCodedQuotient A base hOne E s))
      (codedSourceClass (originalCodedQuotient A base hOne E next)) := by
  refine ⟨originalCodedQuotient A base hOne E s,Quotient.mk'' (Choice A step).p,
    kernel A base hOne E step hE,phase A base hOne E step hE,rfl,
    (codedSourceClass_eq R.iso).symm,?_⟩
  exact actualPhaseRoot_maximalGate _ _ (phase A base hOne E step hE)

/-- Every original stage is retained, or explicitly erased by a whole
fixed-code source isomorphism. The ORIGINAL history is an index of this
type, so intermediate prefixes and their particular chosen gates cannot
be replaced by unrelated endpoint-equivalent stages. -/
inductive Alignment :
    {s next : CertifiedGateTower.ExactPrefix A} →
      History CertifiedGateTower.Step s next → Type (max u v w t + 1)
  | nil (s) : Alignment (.nil s)
  | keep {s middle next} (step : CertifiedGateTower.Step s middle)
      (tail : History CertifiedGateTower.Step middle next)
      (hE : E ≤ certifiedStepOriginalGate A base hOne step)
      (witness : Retained A base hOne E step hE)
      (rest : Alignment tail) : Alignment (.cons step tail)
  | erase {s middle next} (step : CertifiedGateTower.Step s middle)
      (tail : History CertifiedGateTower.Step middle next)
      (hE : ¬ E ≤ certifiedStepOriginalGate A base hOne step)
      (iso : CodedCurrentSourceIso
        (originalCodedQuotient A base hOne E middle)
        (originalCodedQuotient A base hOne E s))
      (rest : Alignment tail) : Alignment (.cons step tail)

theorem alignment {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next) :
    Nonempty (Alignment A base hOne E history) := by
  induction history with
  | nil s => exact ⟨.nil s⟩
  | cons step tail ih =>
    obtain ⟨rest⟩ := ih
    by_cases hE : E ≤ certifiedStepOriginalGate A base hOne step
    · obtain ⟨witness⟩ := retained A base hOne E step hE
      exact ⟨.keep step tail hE witness rest⟩
    · obtain ⟨iso⟩ := Quotient.exact
        (originalCodedQuotient_discardedStep A base hOne E step hE).symm
      exact ⟨.erase step tail hE iso rest⟩

private def castStart {State : Type _} {Step : State → State → Prop}
    {a b c : State} (h : a = b) (history : History Step a c) : History Step b c :=
  h ▸ history

private theorem castStart_length {State : Type _} {Step : State → State → Prop}
    {a b c : State} (h : a = b) (history : History Step a c) :
    (castStart h history).length = history.length := by
  cases h
  rfl

/-- Flatten the witness-aligned trace to the ordinary safe history. A
retained edge uses its OWN kernel/phase witness; a discarded edge merely
transports the subsequent history through its OWN code-preserving iso. -/
def Alignment.projected :
    {s next : CertifiedGateTower.ExactPrefix A} →
    {history : History CertifiedGateTower.Step s next} →
    Alignment A base hOne E history →
    History CodedSafeSourceStep
      (codedSourceClass (originalCodedQuotient A base hOne E s))
      (codedSourceClass (originalCodedQuotient A base hOne E next))
  | _, _, _, .nil _ => .nil _
  | _, _, _, .keep _ _ _ witness rest =>
    .cons (witness.toStep A base hOne E) (rest.projected)
  | _, _, _, .erase _ _ _ iso rest =>
    castStart (codedSourceClass_eq iso) rest.projected

/-- The retained ORIGINAL zero-based indices, in original order. -/
def Alignment.indices :
    {s next : CertifiedGateTower.ExactPrefix A} →
    {history : History CertifiedGateTower.Step s next} →
    Alignment A base hOne E history → List Nat
  | _, _, _, .nil _ => []
  | _, _, _, .keep _ _ _ _ rest => 0 :: rest.indices.map Nat.succ
  | _, _, _, .erase _ _ _ _ rest => rest.indices.map Nat.succ

/-- Original indices selected by EXACTLY the source gate test. This
definition uses the original history alone, independently of its trace. -/
def retainedIndices :
    {s next : CertifiedGateTower.ExactPrefix A} →
    History CertifiedGateTower.Step s next → List Nat
  | _, _, .nil _ => []
  | _, _, .cons step tail =>
    if E ≤ certifiedStepOriginalGate A base hOne step then
      0 :: (retainedIndices tail).map Nat.succ
    else (retainedIndices tail).map Nat.succ

theorem Alignment.indices_eq {s next : CertifiedGateTower.ExactPrefix A}
    {history : History CertifiedGateTower.Step s next}
    (trace : Alignment A base hOne E history) :
    trace.indices = retainedIndices A base hOne E history := by
  induction trace with
  | nil => rfl
  | keep step tail hE witness rest ih =>
    simp [Alignment.indices,retainedIndices,hE,ih]
  | erase step tail hE iso rest ih =>
    simp [Alignment.indices,retainedIndices,hE,ih]

/-- The original gates attached to the actual retained edges. Each
corresponding witness above supplies precisely this gate's G_i/E. -/
def Alignment.gates :
    {s next : CertifiedGateTower.ExactPrefix A} →
    {history : History CertifiedGateTower.Step s next} →
    Alignment A base hOne E history → List (ExactEq A.source base)
  | _, _, _, .nil _ => []
  | _, _, _, .keep step _ _ _ rest =>
    certifiedStepOriginalGate A base hOne step :: rest.gates
  | _, _, _, .erase _ _ _ _ rest => rest.gates

theorem Alignment.gates_eq_filter {s next : CertifiedGateTower.ExactPrefix A}
    {history : History CertifiedGateTower.Step s next}
    (trace : Alignment A base hOne E history) :
    trace.gates = (certifiedHistoryOriginalGates A base hOne history).filter
      (fun G => decide (E ≤ G)) := by
  induction trace with
  | nil => rfl
  | keep step tail hE witness rest ih =>
    simp [Alignment.gates,certifiedHistoryOriginalGates,hE,ih]
  | erase step tail hE iso rest ih =>
    simp [Alignment.gates,certifiedHistoryOriginalGates,hE,ih]

theorem Alignment.projected_length {s next : CertifiedGateTower.ExactPrefix A}
    {history : History CertifiedGateTower.Step s next}
    (trace : Alignment A base hOne E history) :
    trace.projected.length = trace.gates.length := by
  induction trace with
  | nil => rfl
  | keep step tail hE witness rest ih =>
    simp [Alignment.projected,Alignment.gates,History.length,ih]
  | erase step tail hE iso rest ih =>
    simpa only [Alignment.projected,Alignment.gates,castStart_length] using ih

theorem Alignment.indices_length {s next : CertifiedGateTower.ExactPrefix A}
    {history : History CertifiedGateTower.Step s next}
    (trace : Alignment A base hOne E history) :
    trace.indices.length = trace.projected.length := by
  rw [trace.projected_length]
  induction trace with
  | nil => rfl
  | keep step tail hE witness rest ih =>
    simp [Alignment.indices,Alignment.gates,ih]
  | erase step tail hE iso rest ih =>
    simpa [Alignment.indices,Alignment.gates] using ih

theorem Alignment.projected_count {s next : CertifiedGateTower.ExactPrefix A}
    {history : History CertifiedGateTower.Step s next}
    (trace : Alignment A base hOne E history) :
    trace.projected.length =
      (certifiedHistoryOriginalGates A base hOne history).countP
        (fun G => decide (E ≤ G)) := by
  rw [trace.projected_length,trace.gates_eq_filter]
  exact List.countP_eq_length_filter.symm

/-- Every retained stage has an actual valid ORIGINAL index. The trace's
constructors preserve the order as well as its original intermediate source. -/
theorem Alignment.index_lt {s next : CertifiedGateTower.ExactPrefix A}
    {history : History CertifiedGateTower.Step s next}
    (trace : Alignment A base hOne E history)
    (n : Nat) (hn : n ∈ trace.indices) : n < history.length := by
  induction trace generalizing n with
  | nil => simp [Alignment.indices] at hn
  | keep step tail hE witness rest ih =>
    simp only [Alignment.indices,List.mem_cons] at hn
    rcases hn with rfl | hn
    · simp [History.length]
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hn
      have h := ih i hi
      simp only [History.length]
      omega
  | erase step tail hE iso rest ih =>
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hn
    have h := ih i hi
    simp only [History.length]
    omega

end QuotientHistoryProvenance
end
end CCO.ExactEPGeometry
