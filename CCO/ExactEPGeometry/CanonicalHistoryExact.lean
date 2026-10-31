import CCO.ExactEPGeometry.CanonicalStepProduct
import CCO.APCharacter.Towers.HistoryCoherence

/-!
# B062 C28: exact trace geometry over a finite canonical character tower

The history relation is NOT an arbitrary current-source unary refinement.
Every certified canonical step is an ACTUAL `SingleStep.successor` built
from its original full-character source phase; the corresponding
`SingleStep.actualStep` has the genuine reduct and finite-age functor.

Exactness of each such step was proved from the marked-age C22/C23/C25/C27
theorems. This module composes those *proved* interfaces and constructs a
finite terminal history with actual full-character provenance.

Its exact-history reduct is the genuine composition of its chosen actual
step reducts, with no quotient SAP, arbitrary group section or newly
assumed exactness of generic `CurrentSource.ActualStep`.
-/

universe u v w t

namespace CCO.ExactEPGeometry.CanonicalHistoryExact

open APCharacter APCharacter.Towers RigidGroupoid.Geometry
open CCO.ExactEPGeometry

noncomputable section

/-- An individually REAL canonical AP-character source step, including
the complete original phase P and proof that the new current source
is its genuine constructed successor. -/
def CanonicalStep (A B : CurrentSource.{u,v,w,t}) : Prop :=
  ∃ (i : A.Sorts) (K : Kernel A.source i)
    (P : SourcePhase A.source A.homogeneous
      (exactCalculus_of_homogeneous_CCO A.source A.homogeneous A.cco) K),
    B = SourceAge.SingleStep.successor A P

/-- A genuinely sourced actual step together with PROVED two-way RAW
exactness AND nonempty represented (TP) for its literal unary reduct.
This is stronger than an arbitrary `ActualStep` and is not an axiom. -/
def ExactStep (A B : CurrentSource.{u,v,w,t}) : Prop :=
  ∃ step : CurrentSource.ActualStep A B,
    ExactTraceTransport A.source B.source step.reduct ∧
    ExactTraceProduct A.source B.source step.reduct

/-- Every real canonical successor step has the proved exact certificate
and the SAME actual source/finite-age transition from SingleStep. -/
theorem canonical_to_exact
    {A B : CurrentSource.{u,v,w,t}}
    (s : CanonicalStep A B) : ExactStep A B := by
  rcases s with ⟨i,K,P,rfl⟩
  exact ⟨SourceAge.SingleStep.actualStep A P,
    canonical_step_exact_transport A P,
    canonical_step_exact_product A P⟩

/-- A canonical history retains all actual source-step certificates.
No source name or intermediate actual witness is discarded. -/
def exactHistory
    {A B : CurrentSource.{u,v,w,t}}
    (h : History CanonicalStep A B) : History ExactStep A B := by
  induction h with
  | nil A => exact .nil A
  | cons step tail ih => exact .cons (canonical_to_exact step) ih

namespace ExactStep

variable {A B : CurrentSource.{u,v,w,t}}

/-- Choose the real unary reduct from this step's ACTUAL joint certificate,
not from an unrelated map on quotient representatives. -/
def reduct (s : ExactStep A B) : UnaryReduct A.source B.source :=
  (Classical.choose s).reduct

/-- This specific selected reduct satisfies both genuinely proved
nonempty source-to-target and target-to-source RAW exactness directions. -/
theorem transport (s : ExactStep A B) :
    ExactTraceTransport A.source B.source (reduct s) :=
  (Classical.choose_spec s).1

/-- The identical actual witness discharges the typed (TP) equation. -/
theorem product (s : ExactStep A B) :
    ExactTraceProduct A.source B.source (reduct s) :=
  (Classical.choose_spec s).2

/-- The same selected witness also supplies the actual finite-age
transition and exact forgetful functor of this concrete step. -/
def actual (s : ExactStep A B) : CurrentSource.ActualStep A B :=
  Classical.choose s

end ExactStep

/-- The genuine composed original-to-current reduct of this certified
finite history, retaining the old optional colours and bijective global
point map. The zero-stage projection is the actual identity reduct. -/
def historyReduct :
    {A B : CurrentSource.{u,v,w,t}} →
      History ExactStep A B → UnaryReduct A.source B.source
  | A, _, .nil _ => UnaryReduct.identity A.source
  | _, _, .cons step tail =>
      (ExactStep.reduct step).compose (historyReduct tail)

/-- C28 real finite-history transport. Both directions are proved by
induction using each actual step's exact theorem and composition of its
literal unary reducts. In particular all intermediate child sorts are
specified by the history, not existentially erased. -/
theorem history_transport
    {A B : CurrentSource.{u,v,w,t}}
    (h : History ExactStep A B) :
    ExactTraceTransport A.source B.source (historyReduct h) := by
  induction h with
  | nil A =>
      exact ExactTraceTransport.identity A.source
  | cons step tail ih =>
      exact ExactTraceTransport.compose
        (ExactStep.reduct step) (historyReduct tail)
        (ExactStep.transport step) ih

/-- The same actual finite tower also preserves the FULL (TP) equality
with the displayed middle sort at every prefix, whenever BOTH original
exact factor traces are nonempty. This induction uses the already proved
two-way exact-domain source lifts to instantiate (TP) at the next step. -/
theorem history_product
    {A B : CurrentSource.{u,v,w,t}}
    (h : History ExactStep A B) :
    ExactTraceProduct A.source B.source (historyReduct h) := by
  induction h with
  | nil A =>
      exact ExactTraceProduct.identity A.source
  | cons step tail ih =>
      exact ExactTraceProduct.compose
        (ExactStep.reduct step) (historyReduct tail)
        (ExactStep.transport step) (ExactStep.product step)
        (history_transport tail) ih

/-- The ACTUAL full-character history, rather than an arbitrary actual
unary history, inherits the two-way exact RAW trace theorem at its
composite old-reduct projection. This is the C28 iteration statement. -/
theorem canonical_history_transport
    {A B : CurrentSource.{u,v,w,t}}
    (h : History CanonicalStep A B) :
    ExactTraceTransport A.source B.source
      (historyReduct (exactHistory h)) :=
  history_transport (exactHistory h)

/-- Source C28, (TP) half for the actual full-character history. This is
NOT merely exactness of endpoints: it constructs the full current
middle-typed real composite and equates it with the ORIGINAL product trace. -/
theorem canonical_history_product
    {A B : CurrentSource.{u,v,w,t}}
    (h : History CanonicalStep A B) :
    ExactTraceProduct A.source B.source
      (historyReduct (exactHistory h)) :=
  history_product (exactHistory h)

/-- The source's genuine residual interval constructs a canonical exact
successor from its ACTUAL maximal-character phase; this does not claim
that any nominal unary refinement eliminates the obstruction. -/
theorem progress (A : CurrentSource.{u,v,w,t})
    (h : A.Obstruction) :
    ∃ B : CurrentSource.{u,v,w,t}, CanonicalStep A B := by
  obtain ⟨i,K,P,_⟩ := SourceAge.SingleStep.exists_successor A h
  exact ⟨SourceAge.SingleStep.successor A P,i,K,P,rfl⟩

/-- Each actual canonical step strictly decreases the same accepted
integer potential, without a new terminating invariant. -/
theorem decreases {A B : CurrentSource.{u,v,w,t}}
    (step : CanonicalStep A B) : B.potential < A.potential := by
  rcases step with ⟨i,K,P,rfl⟩
  exact SourceAge.SingleStep.potential_decreases A P

/-- Source C28 along the ACTUAL finite terminating canonical safe tower:
the endpoint reduct has a fully discharged two-way RAW exact-trace
transport certificate. Includes the zero-stage case and preserves the
strict potential/length bound of the source's existing progress proof. -/
theorem canonical_terminalisation_exact
    (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ history : History CanonicalStep initial terminal,
        terminal.Terminal ∧
          history.length + terminal.potential ≤ initial.potential ∧
          ExactTraceTransport initial.source terminal.source
            (historyReduct (exactHistory history)) := by
  obtain ⟨terminal,h,ht,hbound⟩ :=
    eliminate_obstructions CanonicalStep CurrentSource.potential
      CurrentSource.Obstruction progress
      (fun {_ _} step => decreases step) initial
  exact ⟨terminal,h,ht,hbound,canonical_history_transport h⟩


/-- The terminating ACTUAL canonical source tower has, at its exact
composed original reduct, both source-to-current exact-domain surjectivity
and the full nonempty-input (TP) equality for all three displayed sorts.
Its phases are genuine AP-only full-character source phases at every step. -/
theorem canonical_terminalisation_geometry
    (initial : CurrentSource.{u,v,w,t}) :
    ∃ terminal : CurrentSource.{u,v,w,t},
      ∃ h : History CanonicalStep initial terminal,
        terminal.Terminal ∧
        h.length + terminal.potential ≤ initial.potential ∧
        ExactTraceTransport initial.source terminal.source
          (historyReduct (exactHistory h)) ∧
        ExactTraceProduct initial.source terminal.source
          (historyReduct (exactHistory h)) := by
  obtain ⟨terminal,h,ht,hbound,hExact⟩ :=
    canonical_terminalisation_exact initial
  exact ⟨terminal,h,ht,hbound,hExact,canonical_history_product h⟩

end
end CCO.ExactEPGeometry.CanonicalHistoryExact
