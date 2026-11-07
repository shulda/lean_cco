import CCO.AutomaticEPCore.NamedIsoReduct
import CCO.AutomaticEPCore.ActualPhaseGateChoice
import CCO.ExactEPGeometry.CodedCurrentSource

/-! The actual B062 coded safe history is received through WHOLE source
isomorphisms and its SAME actual phases. Every prefix retains a literal
fixed-original reduct, both proved RAW directions and full typed TP.
No new tower, source or character provider is an input. -/

universe u v w t z
namespace CCO.AutomaticEPCore
open CCO.APCharacter CCO.APCharacter.Towers CCO.ExactEPGeometry
open CCO.RigidGroupoid.Geometry
noncomputable section

namespace IsoGateTower

variable {A : CurrentSource.{u,v,w,t}}

/-- Source renamings are explicit zero-cost steps; real splitting steps
retain an actual certified GateChoice and its precise successor. -/
inductive StepData : CertifiedGateTower.ExactPrefix A →
    CertifiedGateTower.ExactPrefix A → Type (max (u+1) (v+1) (w+1) (t+1))
  | rename (s : CertifiedGateTower.ExactPrefix A)
      {B : CurrentSource.{u,v,w,t}} (I : NamedCurrentSourceIso s.current B) :
      StepData s (namedIsoExactPrefix s I)
  | split {s next : CertifiedGateTower.ExactPrefix A}
      (step : CertifiedGateTower.Step s next) : StepData s next

def Step (s next : CertifiedGateTower.ExactPrefix A) : Prop := Nonempty (StepData s next)

theorem Step.rename (s : CertifiedGateTower.ExactPrefix A)
    {B : CurrentSource.{u,v,w,t}} (I : NamedCurrentSourceIso s.current B) :
    Step s (namedIsoExactPrefix s I) := ⟨StepData.rename s I⟩

theorem Step.split {s next : CertifiedGateTower.ExactPrefix A}
    (step : CertifiedGateTower.Step s next) : Step s next := ⟨StepData.split step⟩

end IsoGateTower

def codedExactPrefix {Code : Type z} {A : CurrentSource.{u,v,w,t}}
    (rootCode : Sigma A.Point → Sigma A.Point → Code)
    (s : CertifiedGateTower.ExactPrefix A) : CodedCurrentSource.{u,v,w,t} Code where
  current := s.current
  code := fun p q => rootCode (s.reduct.project p) (s.reduct.project q)

/-- Receiving an actual code-preserving source iso preserves the VALUE
of each fixed original predicate through the constructed inverse reduct. -/
def codedExactPrefix_reindex_iso {Code : Type z} {A : CurrentSource.{u,v,w,t}}
    (rootCode : Sigma A.Point → Sigma A.Point → Code)
    (s : CertifiedGateTower.ExactPrefix A)
    {B : CodedCurrentSource.{u,v,w,t} Code}
    (I : CodedCurrentSourceIso (codedExactPrefix rootCode s) B) :
    CodedCurrentSourceIso
      (codedExactPrefix rootCode (namedIsoExactPrefix s I.toNamedCurrentSourceIso)) B where
  toNamedCurrentSourceIso := NamedCurrentSourceIso.refl B.current
  code_eq := by
    change ∀ p q : Sigma B.current.Point, B.code p q = rootCode
      (s.reduct.project ((namedIsoReduct I.toNamedCurrentSourceIso).project p))
      (s.reduct.project ((namedIsoReduct I.toNamedCurrentSourceIso).project q))
    intro p q
    rw [namedIsoReduct_project,namedIsoReduct_project]
    exact (congrArg₂ B.code (I.points.apply_symm_apply p).symm
      (I.points.apply_symm_apply q).symm).trans
      (I.code_eq (I.points.symm p) (I.points.symm q))

/-- The SAME actual phase survives receiving; the isomorphism fixes the
complete actual successor points, so it also fixes every root predicate. -/
def codedExactPrefix_reindex_phase_iso {Code : Type z} {A : CurrentSource.{u,v,w,t}}
    (rootCode : Sigma A.Point → Sigma A.Point → Code)
    (s : CertifiedGateTower.ExactPrefix A)
    {B : CodedCurrentSource.{u,v,w,t} Code}
    (I : CodedCurrentSourceIso (codedExactPrefix rootCode s) B)
    {r : B.current.Sorts} {K : Kernel B.current.source r}
    (phase : SourcePhase B.current.source B.current.homogeneous
      (exactCalculus_of_homogeneous_CCO B.current.source B.current.homogeneous B.current.cco) K) :
    CodedCurrentSourceIso
      (codedExactPrefix rootCode
        (actualPhasePrefix (namedIsoExactPrefix s I.toNamedCurrentSourceIso) phase))
      (B.successor phase) where
  toNamedCurrentSourceIso := NamedCurrentSourceIso.refl _
  code_eq := by
    intro p q
    exact (codedExactPrefix_reindex_iso rootCode s I).code_eq
      ((SourceAge.SingleStep.projection B.current phase).project p)
      ((SourceAge.SingleStep.projection B.current phase).project q)

/-- Receive EVERY edge of the genuine coded safe history. Actual source
isos construct real exact prefixes; the EXISTING phase constructs its
own certified choice. Nothing identifies a merely endpoint-equivalent
phase or an arbitrary selected generating subgroup with the whole phase. -/
theorem coded_safe_history_exact_prefix_receiving
    {Code : Type z} (A : CurrentSource.{u,v,w,t})
    (rootCode : Sigma A.Point → Sigma A.Point → Code)
    {a b : CodedSourceClass.{u,v,w,t} Code}
    (history : History CodedSafeSourceStep a b) :
    ∀ s : CertifiedGateTower.ExactPrefix A,
      codedSourceClass (codedExactPrefix rootCode s) = a →
      ∃ next : CertifiedGateTower.ExactPrefix A,
        Nonempty (History IsoGateTower.Step s next) ∧
        codedSourceClass (codedExactPrefix rootCode next) = b := by
  induction history with
  | nil a =>
    intro s same
    exact ⟨s,⟨.nil s⟩,same⟩
  | @cons a b c step tail ih =>
    intro s same
    obtain ⟨B,r,K,phase,hB,hNext,_⟩ := step
    have classes : codedSourceClass (codedExactPrefix rootCode s) = codedSourceClass B :=
      same.trans hB.symm
    obtain ⟨I⟩ : Nonempty (CodedCurrentSourceIso (codedExactPrefix rootCode s) B) :=
      Quotient.exact classes
    let mid := namedIsoExactPrefix s I.toNamedCurrentSourceIso
    obtain ⟨choice,choiceEq⟩ := actual_phase_has_certified_gate_choice A mid K phase
    let next := CertifiedGateTower.successor mid choice
    have nextClass : codedSourceClass (codedExactPrefix rootCode next) = b := by
      dsimp only [next]
      rw [choiceEq]
      exact (codedSourceClass_eq (codedExactPrefix_reindex_phase_iso rootCode s I phase)).trans hNext
    obtain ⟨last,⟨rest⟩,lastClass⟩ := ih next nextClass
    refine ⟨last,⟨.cons (IsoGateTower.Step.rename s I.toNamedCurrentSourceIso)
      (.cons (IsoGateTower.Step.split ⟨choice,rfl⟩) rest)⟩,lastClass⟩

end
end CCO.AutomaticEPCore
