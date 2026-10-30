import CCO.APCharacter.SourceAge.Identification
import CCO.APCharacter.SourceAge.CharacterRank
import CCO.APCharacter.SourceAge.UnarySourceCCO
import CCO.APCharacter.SourceAge.UnaryTransition
import CCO.APCharacter.Towers.CurrentParity

/-! The actual CURRENT-source successor of a finite-interval character
split. The old-reduct isomorphism, whole homogeneity, countability, CCO and
strict rank drop are constructed, rather than supplied step callbacks. -/
universe u v w t
namespace CCO.APCharacter.SourceAge.SingleStep
open RigidGroupoid.Geometry UnarySource
noncomputable section
variable (B : Towers.CurrentSource.{u,v,w,t})
variable {i : B.Sorts} {K : Kernel B.source i}
variable (P : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) K)

def identification : Identification B.source B.homogeneous (P.completion_property B.cco) := by
  letI := B.countable
  exact actualIdentification P B.cco

def successor : Towers.CurrentSource.{u,v,w,t} where
  Sorts := Rank.Child (β (identification B P))
  Point := Rank.Point (β (identification B P)) (tag (identification B P))
  source := source (identification B P)
  G := FullGroup (identification B P)
  group := inferInstance
  action := by intro c; infer_instance
  homogeneous := homogeneous (identification B P)
  countable := by
    letI := B.countable
    intro c
    exact countable_child (identification B P) c
  cco := semanticCCO (identification B P)

theorem potential_decreases : (successor B P).potential < B.potential := by
  exact CharacterRank.actual_rank_drop P B.cco (identification B P)

/-- A true residual interval supplies an ACTUAL next source with all
source properties and strict decrease, not merely a next-rank number. -/
theorem exists_successor (h : B.Obstruction) :
    ∃ (i : B.Sorts) (K : Kernel B.source i)
      (P : SourcePhase B.source B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) K),
      (successor B P).potential < B.potential := by
  obtain ⟨i,K,⟨P⟩⟩ := B.phase_of_obstruction h
  exact ⟨i,K,P,potential_decreases B P⟩

def projection : Towers.UnaryReduct B.source (successor B P).source :=
  actualProjection (identification B P)

def transition : Towers.UnaryTransition B.finiteAge (successor B P).finiteAge :=
  actual_unary_transition (identification B P) P.finite_seed_extension

theorem transition_forget : (transition B P).forget = (projection B P).forget := rfl

def step : Towers.CurrentSource.Step Towers.CurrentSource.finiteAge B (successor B P) where
  unary := transition B P
  potential_lt := potential_decreases B P

/-- The generic CURRENT-source progress premise is now ACTUALLY discharged.
The constructor invokes the source parity proof and the full marked/Fraisse
source pipeline, not an arbitrary next-stage or principal theorem provider. -/
theorem progress (h : B.Obstruction) :
    ∃ next : Towers.CurrentSource.{u,v,w,t},
      Nonempty (Towers.CurrentSource.Step Towers.CurrentSource.finiteAge B next) := by
  obtain ⟨i,K,⟨P⟩⟩ := B.phase_of_obstruction h
  exact ⟨successor B P,⟨step B P⟩⟩

end
end CCO.APCharacter.SourceAge.SingleStep
