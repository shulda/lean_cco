import CCO.CloneTupleGeometry.OwnerSourceCCO
import CCO.CloneTupleGeometry.OwnerReasonableness
import CCO.CloneTupleGeometry.OwnerRankDrop
import CCO.APCharacter.Towers.CurrentParity
import CCO.APCharacter.Towers.ProjectionComposition
import CCO.PairSafeSplit.Terminal.Current

/-! B064 C96: the genuine maximal-character clone tower for FINITE owners.
Every successor is the actual marked source's owner quotient, with its
proved clone-constant phase labels. Owner finiteness is preserved by the
literal child subtype. No infinite-owner chart or OwnerStage API is used. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.UnfilteredEP
open CloneTupleGeometry APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry TerminalPowers CategoryTheory
noncomputable section

structure FiniteOwnerStage where
  Sorts : Type u
  Point : Sorts → Type v
  source : AtomicSource.{u,v,w} Sorts Point
  homogeneous : HomogeneousSource source (FullAut source)
  ap : AgeAP source
  cco : SemanticCCO.{u,v,max u v,w} source
  finite : ∀ i, Finite (Point i)

namespace FiniteOwnerStage

def cloneCurrent (B : FiniteOwnerStage.{u,v,w}) : CurrentSource where
  Sorts := B.Sorts
  Point := CloneSAP.Carrier B.Point
  source := CloneSAP.source B.source
  G := FullAut (CloneSAP.source B.source)
  homogeneous := CloneSAP.homogeneous B.source B.homogeneous
  countable := by
    letI := B.finite
    intro i
    infer_instance
  cco := CloneSAP.CCO.cco_forward B.source B.cco

def cloneSafeCurrent (B : FiniteOwnerStage.{u,v,w}) : PairSafeSplit.Terminal.CurrentSource :=
  ⟨B.cloneCurrent,CloneSAP.strong_amalgamation B.source B.ap⟩

def potential (B : FiniteOwnerStage.{u,v,w}) : ℕ := B.cloneCurrent.potential
def Obstruction (B : FiniteOwnerStage.{u,v,w}) : Prop := B.cloneCurrent.Obstruction
def Terminal (B : FiniteOwnerStage.{u,v,w}) : Prop := B.cloneCurrent.Terminal
def finiteAge (B : FiniteOwnerStage.{u,v,w}) : UnaryAge.{0,0} :=
  ⟨Age.Chart B.source (Age.zeroMask B.source),Age.chartCategory B.source (Age.zeroMask B.source)⟩

variable (B : FiniteOwnerStage.{u,v,w})
variable {i : B.Sorts} {K : Kernel (CloneSAP.source B.source) i}
variable (P : SourcePhase (CloneSAP.source B.source)
  (CloneSAP.homogeneous B.source B.homogeneous)
  (exactCalculus_of_homogeneous_CCO B.cloneCurrent.source B.cloneCurrent.homogeneous B.cloneCurrent.cco) K)

def identification : CloneMarkedIdentification B.source B.homogeneous
    (exactCalculus_of_homogeneous_CCO B.cloneCurrent.source B.cloneCurrent.homogeneous B.cloneCurrent.cco)
    P B.cco := by
  letI := B.finite
  exact actualCloneIdentification B.source B.homogeneous _ P B.cco

/-- The next state is the actual marked source's owner quotient, whose
canonical pure clone is completely isomorphic to that marked source. -/
def successor : FiniteOwnerStage.{u,v,w} where
  Sorts := Rank.Child (UnarySource.β (completion := P.completion_property B.cloneCurrent.cco) (B.identification P))
  Point := OwnerChild B.source B.homogeneous _ P B.cco (B.identification P)
  source := owner_child_source B.source B.homogeneous B.ap _ P B.cco (B.identification P)
  homogeneous := actual_marked_owner_homogeneous B.source B.homogeneous B.ap _ P B.cco (B.identification P)
  ap := actual_marked_owner_ageAP B.source B.homogeneous B.ap _ P B.cco (B.identification P)
  cco := actual_marked_owner_semanticCCO B.source B.homogeneous B.ap _ P B.cco (B.identification P)
  finite := by
    letI := B.finite
    intro c
    infer_instance

def successorReduct : UnaryReduct B.source (B.successor P).source :=
  ownerProjection B.source B.homogeneous B.ap _ P B.cco (B.identification P)

def successorUnary : UnaryTransition B.finiteAge (B.successor P).finiteAge :=
  owner_unary_transition B.source B.homogeneous B.ap _ P B.cco (B.identification P)

theorem successor_forget : (B.successorUnary P).forget = (B.successorReduct P).forget := rfl

theorem successor_potential_lt : (B.successor P).potential < B.potential := by
  exact owner_clone_actual_rank_drop B.source B.homogeneous B.ap _ P B.cco (B.identification P)

/-- Every edge stores an ACTUAL character phase and has exactly its
constructed successor. Thus arbitrary reasonable unary labels cannot
enter the terminal history. -/
inductive SafeStep : FiniteOwnerStage.{u,v,w} → FiniteOwnerStage.{u,v,w} → Type _
  | phase (B : FiniteOwnerStage.{u,v,w}) {i : B.Sorts}
      {K : Kernel (CloneSAP.source B.source) i}
      (P : SourcePhase (CloneSAP.source B.source)
        (CloneSAP.homogeneous B.source B.homogeneous)
        (exactCalculus_of_homogeneous_CCO B.cloneCurrent.source
          B.cloneCurrent.homogeneous B.cloneCurrent.cco) K) : SafeStep B (B.successor P)

namespace SafeStep
def reduct {B D : FiniteOwnerStage.{u,v,w}} (s : SafeStep B D) : UnaryReduct B.source D.source := by
  cases s with
  | phase P => exact B.successorReduct P

def unary {B D : FiniteOwnerStage.{u,v,w}} (s : SafeStep B D) : UnaryTransition B.finiteAge D.finiteAge := by
  cases s with
  | phase P => exact B.successorUnary P

theorem forget_eq {B D : FiniteOwnerStage.{u,v,w}} (s : SafeStep B D) :
    s.unary.forget = s.reduct.forget := by
  cases s
  rfl

theorem potential_lt {B D : FiniteOwnerStage.{u,v,w}} (s : SafeStep B D) : D.potential < B.potential := by
  cases s with
  | phase P => exact B.successor_potential_lt P
end SafeStep

abbrev Next (B D : FiniteOwnerStage.{u,v,w}) := Nonempty (SafeStep B D)

/-- A real finite relative interval supplies the actual maximal-character
phase, its source construction and the already proved strict rank drop. -/
theorem progress (h : B.Obstruction) : ∃ D, Next B D := by
  obtain ⟨i,K,⟨P⟩⟩ := B.cloneCurrent.phase_of_obstruction h
  exact ⟨B.successor P,⟨SafeStep.phase B P⟩⟩

def historyReduct {B D : FiniteOwnerStage.{u,v,w}} (h : History Next B D) : UnaryReduct B.source D.source := by
  induction h with
  | nil B => exact UnaryReduct.identity B.source
  | cons hs tail ih => exact (Classical.choice hs).reduct.compose ih

def historyUnary {B D : FiniteOwnerStage.{u,v,w}} (h : History Next B D) :
    UnaryTransition B.finiteAge D.finiteAge :=
  finiteUnaryComposite finiteAge (fun hs => (Classical.choice hs).unary) h

theorem history_forget_eq {B D : FiniteOwnerStage.{u,v,w}} (h : History Next B D) :
    (historyReduct h).forget = (historyUnary h).forget := by
  induction h with
  | nil B => exact UnaryReduct.identity_forget B.source
  | cons hs tail ih =>
    change ((Classical.choice hs).reduct.compose (historyReduct tail)).forget =
      (historyUnary tail).forget ⋙ (Classical.choice hs).unary.forget
    rw [UnaryReduct.compose_forget,ih,← (Classical.choice hs).forget_eq]
    rfl

def historyTransition {B D : FiniteOwnerStage.{u,v,w}} (h : History Next B D) :
    UnaryTransition B.finiteAge D.finiteAge where
  forget := (historyReduct h).forget
  reasonable := by rw [history_forget_eq]; exact (historyUnary h).reasonable
  reductSurjective := by rw [history_forget_eq]; exact (historyUnary h).reductSurjective
  precompact := by rw [history_forget_eq]; exact (historyUnary h).precompact

/-- Finite clone-stable terminalisation with no progress/provider premise.
The endpoint still has finite owners and actual homogeneous
AP+HOM CCO; its pure clone has SAP and no finite proper relative interval.
The same literal owner reduct is the reasonable finite unary expansion. -/
theorem finite_safe_terminalisation :
    ∃ D : FiniteOwnerStage.{u,v,w}, ∃ h : History Next B D,
      D.Terminal ∧ h.length + D.potential ≤ B.potential ∧
      ∃ reduct : UnaryReduct B.source D.source,
        ∃ unary : UnaryTransition B.finiteAge D.finiteAge,
          unary.forget = reduct.forget := by
  obtain ⟨D,h,ht,hbound⟩ := eliminate_obstructions Next potential Obstruction progress
    (fun hs => (Classical.choice hs).potential_lt) B
  exact ⟨D,h,ht,hbound,historyReduct h,historyTransition h,rfl⟩

end FiniteOwnerStage

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- The actual finite original source, with its full homogeneous action. -/
def initialFiniteOwnerStage (finite : ∀ i, Finite (X i)) : FiniteOwnerStage.{u,v,w} where
  Sorts := ι
  Point := X
  source := S
  homogeneous := full_homogeneous S H
  ap := ap
  cco := cco
  finite := finite

end
end CCO.UnfilteredEP
