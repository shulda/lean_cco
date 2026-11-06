import CCO.CloneTupleGeometry.OwnerSourceCCO
import CCO.CloneTupleGeometry.OwnerChildInfinitude
import CCO.CloneTupleGeometry.OwnerReasonableness
import CCO.CloneTupleGeometry.OwnerRankDrop
import CCO.APCharacter.Towers.CurrentParity
import CCO.APCharacter.Towers.ProjectionComposition
import CCO.PairSafeSplit.Terminal.Current

/-! Actual finite safe character iteration in canonical pure-clone form.
Each step is the genuine B047 marked source followed by its proved owner
quotient. Countably infinite owner children, ordinary owner AP and HOM CCO
are retained. Strict descent counts the actual canonical clone palettes.
There is no arbitrary successor, source instance, rank or unary functor
callback, and no owner SAP field. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w
namespace CCO.CloneTupleGeometry
open APCharacter APCharacter.SourceAge APCharacter.Towers
open RigidGroupoid.Geometry TerminalPowers CategoryTheory
noncomputable section

structure OwnerStage where
  Sorts : Type u
  Point : Sorts → Type v
  source : AtomicSource.{u,v,w} Sorts Point
  homogeneous : HomogeneousSource source (FullAut source)
  ap : AgeAP source
  cco : SemanticCCO.{u,v,max u v,w} source
  countable : ∀ i, Countable (Point i)
  infinite : ∀ i, Infinite (Point i)

namespace OwnerStage

def cloneCurrent (B : OwnerStage.{u,v,w}) : CurrentSource where
  Sorts := B.Sorts
  Point := CloneSAP.Carrier B.Point
  source := CloneSAP.source B.source
  G := FullAut (CloneSAP.source B.source)
  homogeneous := CloneSAP.homogeneous B.source B.homogeneous
  countable := by
    letI := B.countable
    intro i
    infer_instance
  cco := CloneSAP.CCO.cco_forward B.source B.cco

def cloneSafeCurrent (B : OwnerStage.{u,v,w}) : PairSafeSplit.Terminal.CurrentSource :=
  ⟨B.cloneCurrent,CloneSAP.strong_amalgamation B.source B.ap⟩

def potential (B : OwnerStage.{u,v,w}) : ℕ := B.cloneCurrent.potential
def Obstruction (B : OwnerStage.{u,v,w}) : Prop := B.cloneCurrent.Obstruction
def Terminal (B : OwnerStage.{u,v,w}) : Prop := B.cloneCurrent.Terminal
def finiteAge (B : OwnerStage.{u,v,w}) : UnaryAge.{0,0} :=
  ⟨Age.Chart B.source (Age.zeroMask B.source),Age.chartCategory B.source (Age.zeroMask B.source)⟩

variable (B : OwnerStage.{u,v,w})
variable {i : B.Sorts} {K : Kernel (CloneSAP.source B.source) i}
variable (P : SourcePhase (CloneSAP.source B.source)
  (CloneSAP.homogeneous B.source B.homogeneous)
  (exactCalculus_of_homogeneous_CCO B.cloneCurrent.source B.cloneCurrent.homogeneous B.cloneCurrent.cco) K)

def identification : CloneMarkedIdentification B.source B.homogeneous
    (exactCalculus_of_homogeneous_CCO B.cloneCurrent.source B.cloneCurrent.homogeneous B.cloneCurrent.cco)
    P B.cco := by
  letI := B.countable
  exact actualCloneIdentification B.source B.homogeneous _ P B.cco

/-- The next state is the actual marked source's owner quotient, whose
canonical pure clone is completely isomorphic to that marked source. -/
def successor : OwnerStage.{u,v,w} where
  Sorts := Rank.Child (UnarySource.β (B.identification P))
  Point := OwnerChild B.source B.homogeneous _ P B.cco (B.identification P)
  source := owner_child_source B.source B.homogeneous B.ap _ P B.cco (B.identification P)
  homogeneous := actual_marked_owner_homogeneous B.source B.homogeneous B.ap _ P B.cco (B.identification P)
  ap := actual_marked_owner_ageAP B.source B.homogeneous B.ap _ P B.cco (B.identification P)
  cco := actual_marked_owner_semanticCCO B.source B.homogeneous B.ap _ P B.cco (B.identification P)
  countable := by
    letI := B.countable
    intro c
    infer_instance
  infinite := by
    letI := B.infinite
    exact marked_all_owner_children_infinite B.source B.homogeneous B.ap _ P B.cco (B.identification P)

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
inductive SafeStep : OwnerStage.{u,v,w} → OwnerStage.{u,v,w} → Type _
  | phase (B : OwnerStage.{u,v,w}) {i : B.Sorts}
      {K : Kernel (CloneSAP.source B.source) i}
      (P : SourcePhase (CloneSAP.source B.source)
        (CloneSAP.homogeneous B.source B.homogeneous)
        (exactCalculus_of_homogeneous_CCO B.cloneCurrent.source
          B.cloneCurrent.homogeneous B.cloneCurrent.cco) K) : SafeStep B (B.successor P)

namespace SafeStep
def reduct {B D : OwnerStage.{u,v,w}} (s : SafeStep B D) : UnaryReduct B.source D.source := by
  cases s with
  | phase B P => exact B.successorReduct P

def unary {B D : OwnerStage.{u,v,w}} (s : SafeStep B D) : UnaryTransition B.finiteAge D.finiteAge := by
  cases s with
  | phase B P => exact B.successorUnary P

theorem forget_eq {B D : OwnerStage.{u,v,w}} (s : SafeStep B D) :
    s.unary.forget = s.reduct.forget := by
  cases s
  rfl

theorem potential_lt {B D : OwnerStage.{u,v,w}} (s : SafeStep B D) : D.potential < B.potential := by
  cases s with
  | phase B P => exact B.successor_potential_lt P
end SafeStep

abbrev Next (B D : OwnerStage.{u,v,w}) := Nonempty (SafeStep B D)

/-- A real finite relative interval supplies the actual maximal-character
phase, its source construction and the already proved strict rank drop. -/
theorem progress (h : B.Obstruction) : ∃ D, Next B D := by
  obtain ⟨i,K,⟨P⟩⟩ := B.cloneCurrent.phase_of_obstruction h
  exact ⟨B.successor P,⟨SafeStep.phase B P⟩⟩

def historyReduct {B D : OwnerStage.{u,v,w}} (h : History Next B D) : UnaryReduct B.source D.source := by
  induction h with
  | nil B => exact UnaryReduct.identity B.source
  | cons hs tail ih => exact (Classical.choice hs).reduct.compose ih

def historyUnary {B D : OwnerStage.{u,v,w}} (h : History Next B D) :
    UnaryTransition B.finiteAge D.finiteAge :=
  finiteUnaryComposite finiteAge (fun hs => (Classical.choice hs).unary) h

theorem history_forget_eq {B D : OwnerStage.{u,v,w}} (h : History Next B D) :
    (historyReduct h).forget = (historyUnary h).forget := by
  induction h with
  | nil B => exact UnaryReduct.identity_forget B.source
  | cons hs tail ih =>
    change ((Classical.choice hs).reduct.compose (historyReduct tail)).forget =
      (historyUnary tail).forget ⋙ (Classical.choice hs).unary.forget
    rw [UnaryReduct.compose_forget,ih,← (Classical.choice hs).forget_eq]
    rfl

def historyTransition {B D : OwnerStage.{u,v,w}} (h : History Next B D) :
    UnaryTransition B.finiteAge D.finiteAge where
  forget := (historyReduct h).forget
  reasonable := by rw [history_forget_eq]; exact (historyUnary h).reasonable
  reductSurjective := by rw [history_forget_eq]; exact (historyUnary h).reductSurjective
  precompact := by rw [history_forget_eq]; exact (historyUnary h).precompact

/-- Finite clone-stable terminalisation with no progress/provider premise.
The endpoint still has countably infinite owners and actual homogeneous
AP+HOM CCO; its pure clone has SAP and no finite proper relative interval.
The same literal owner reduct is the reasonable finite unary expansion. -/
theorem finite_safe_terminalisation :
    ∃ D : OwnerStage.{u,v,w}, ∃ h : History Next B D,
      D.Terminal ∧ h.length + D.potential ≤ B.potential ∧
      ∃ reduct : UnaryReduct B.source D.source,
        ∃ unary : UnaryTransition B.finiteAge D.finiteAge,
          unary.forget = reduct.forget := by
  obtain ⟨D,h,ht,hbound⟩ := eliminate_obstructions Next potential Obstruction progress
    (fun hs => (Classical.choice hs).potential_lt) B
  exact ⟨D,h,ht,hbound,historyReduct h,historyTransition h,rfl⟩

end OwnerStage

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type*} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) (ap : AgeAP S)
variable (cco : SemanticCCO.{u,v,max u v,w} S)

/-- Original hypotheses construct the initial owner state; replacing its
acting group by the actual full automorphism group is proved from H. -/
def initialOwnerStage (countable : ∀ i, Countable (X i))
    (infinite : ∀ i, Infinite (X i)) : OwnerStage.{u,v,w} where
  Sorts := ι
  Point := X
  source := S
  homogeneous := full_homogeneous S H
  ap := ap
  cco := cco
  countable := countable
  infinite := infinite

/-- Original-source finite safe clone terminalisation, including the
actual owner expansion and its finite phase history. This theorem has
only the original countably infinite homogeneous AP+HOM CCO hypotheses. -/
theorem actual_owner_finite_safe_terminalisation
    (countable : ∀ i, Countable (X i)) (infinite : ∀ i, Infinite (X i)) :
    ∃ D : OwnerStage.{u,v,w},
      ∃ h : History OwnerStage.Next (initialOwnerStage S H ap cco countable infinite) D,
        D.Terminal ∧
        h.length + D.potential ≤ (initialOwnerStage S H ap cco countable infinite).potential ∧
        ∃ reduct : UnaryReduct S D.source,
          ∃ unary : UnaryTransition
            (initialOwnerStage S H ap cco countable infinite).finiteAge D.finiteAge,
            unary.forget = reduct.forget :=
  (initialOwnerStage S H ap cco countable infinite).finite_safe_terminalisation

end
end CCO.CloneTupleGeometry
