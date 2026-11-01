import CCO.ExactEPGeometry.OriginalGateKernelMeet
import CCO.ExactEPGeometry.OriginalCommonGateEquality
import CCO.ExactEPGeometry.CertifiedGateTower

/-!
# B062 C59–C60: common ORIGINAL RAW-exact kernel from ACTUAL safe history

A genuine `CertifiedGateTower.Step s t` contains an existential
`GateChoice s` with the SAME current maximal gate M, source-selected
odd orbital, old Y/U certificates, actual SourcePhase and literal
successor equality. We extract ONLY a witness of THAT certified step,
and record its actual greatest original exact L_p(M.kernel); it is
not an independently selected gate.

For a fixed ONE-original-sort source, these genuine old gates are
reindexed by actual original sort equalities to the same OLD carrier.
The finite real History provides their full list, with repetitions.
The common kernel is the TRUE finite `ExactEq` meet. A zero-stage
history has empty gate list and common kernel original Top.

C61–C64 still require proving that this precise original exact
relation is exactly the largest one preserving EVERY final unary bit;
that nontrivial character/dominance argument is not assumed here.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open CCO.ExactEPGeometry.CertifiedGateTower
open RigidGroupoid.Geometry

noncomputable section

/-- The genuine gate of one ACTUAL certified safe step, transported
to the fixed original source sort. Classical choice selects a witness
of the EXISTING `Step` certificate; it does NOT select a new independent
MaximalGate or SourcePhase. -/
def certifiedStepOriginalGate
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) :
    ExactEq A.source base := by
  let choice : CertifiedGateTower.GateChoice s := Classical.choose step
  let F : ExactEq s.current.source choice.p :=
    ⟨choice.M.kernel, choice.M.maximal.1.1⟩
  let G : ExactEq A.source (s.reduct.parent choice.p) :=
    PrefixExactLargestLift.largest A s.current
      s.reduct s.transport s.product choice.p F
  exact oldExactEqCast A.source
    (hOne (s.reduct.parent choice.p)) G

/-- The selected step gate above really belongs to its ACTUAL
source-to-successor step, whose phase is the one retained by the
`GateChoice`. No arbitrary re-selection of the finite-age expansion. -/
theorem certifiedStep_witness_is_actual_successor
    {A : CurrentSource.{u,v,w,t}}
    {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) :
    next = CertifiedGateTower.successor s (Classical.choose step) :=
  Classical.choose_spec step

/-- Original exact gates attached to EVERY source-certified step of
this real finite history, not just its terminal source or a chosen
generating subset of the connected full groupoid. The original carrier
is fixed by the actual one-sort equality. -/
def certifiedHistoryOriginalGates
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i) :
    {s next : CertifiedGateTower.ExactPrefix A} →
      History CertifiedGateTower.Step s next →
        List (ExactEq A.source base)
  | _, _, .nil _ => []
  | _, _, .cons step tail =>
      certifiedStepOriginalGate A base hOne step ::
        certifiedHistoryOriginalGates A base hOne tail

/-- The number of actual original gates is the exact finite length of
the certified source history, including the zero-step case. -/
theorem certifiedHistoryOriginalGates_length
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next) :
    (certifiedHistoryOriginalGates A base hOne history).length =
      history.length := by
  induction history with
  | nil _ => rfl
  | cons step tail ih =>
      simp [certifiedHistoryOriginalGates, History.length, ih]

/-- The actual C59 common original full RAW-exact equivalence, with
every factor sourced from a genuine GateChoice along the whole history.
This is never a meet in the larger invariant-equivalence lattice. -/
def certifiedHistoryCommonOriginalKernel
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next) :
    ExactEq A.source base :=
  originalExactGateMeet A.source base
    (certifiedHistoryOriginalGates A base hOne history)

/-- A genuinely empty actual character history has original Top as
its common exact gate, never logical identity by convention. -/
@[simp] theorem certifiedHistoryCommonOriginalKernel_nil
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    (s : CertifiedGateTower.ExactPrefix A) :
    certifiedHistoryCommonOriginalKernel A base hOne
      (History.nil s) = (⊤ : ExactEq A.source base) := rfl

/-- The common certified-history gate is the greatest ORIGINAL
full RAW-exact equivalence below EVERY actual selected old gate. -/
theorem certifiedHistoryCommonOriginalKernel_greatest
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next)
    (E : ExactEq A.source base) :
    E ≤ certifiedHistoryCommonOriginalKernel A base hOne history ↔
      ∀ G ∈ certifiedHistoryOriginalGates A base hOne history, E ≤ G :=
  originalExactGateMeet_greatest A.source base
    (certifiedHistoryOriginalGates A base hOne history) E

/-- C59's real original pair relation is exactly the intersection
of ALL selected old gates, with true old equality retained. -/
theorem certifiedHistoryCommonOriginalKernel_iff
    (A : CurrentSource.{u,v,w,t})
    (base : A.Sorts)
    (hOne : ∀ i : A.Sorts, base = i)
    {s next : CertifiedGateTower.ExactPrefix A}
    (history : History CertifiedGateTower.Step s next)
    (x y : A.Point base) :
    certifiedHistoryCommonOriginalKernel A base hOne history x y ↔
      ∀ G ∈ certifiedHistoryOriginalGates A base hOne history, G x y :=
  originalExactGateMeet_iff A.source base
    (certifiedHistoryOriginalGates A base hOne history) x y

end
end CCO.ExactEPGeometry
