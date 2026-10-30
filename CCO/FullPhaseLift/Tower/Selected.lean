import CCO.FullPhaseLift.Tower.SingleStep
import CCO.FullPhaseLift.BinarySource.MarkedComparisonSourceIso
import CCO.PairSafeSplit.Terminal.Elimination

/-! Every FULL step retains the concrete ORIGINAL parity gate selected
by B047, the actual full marked realization and its proved pair comparison. -/
universe m
namespace CCO.FullPhaseLift.Tower
open Canonical APCharacter APCharacter.Towers RigidGroupoid.Geometry
noncomputable section
variable {M : Type m} [Countable M]

namespace SingleStep
variable (A : CurrentSource M)
variable {i : A.pair.base.Sorts} {K : RigidGroupoid.Geometry.Kernel A.pair.base.source i}
variable (P : SourcePhase A.pair.base.source A.pair.base.homogeneous
  (exactCalculus_of_homogeneous_CCO A.pair.base.source A.pair.base.homogeneous A.pair.base.cco) K)

/-- The comparison used by progress is ACTUALLY constructed from the
same full model's finite age, raw interface and native pair back-and-forth. -/
def actualComparison : Full.SourceIso (source (fullTable A P) (full_symmetric A P))
    (pairChild A P).base.source := by
  letI : ∀ j, MulAction A.pair.base.G (Carrier A.table j) := A.pair.base.action
  apply comparison A P
  exact BinarySource.MarkedComparison.nativeSourceIso A.table A.symmetric P A.pair.base.cco
    (APCharacter.SourceAge.SingleStep.identification A.pair.base P) (classSAP A P) (oldIso A P)
    (A.normal.to_strict A.table A.symmetric)

def successor : CurrentSource M := current A P (actualComparison A P)

theorem potential_lt : (successor A P).potential < A.potential := by
  rw [show (successor A P).potential = (pairChild A P).potential from potential_eq A P (actualComparison A P)]
  exact A.pair.actual_potential_drop P
end SingleStep

structure SelectedStep (A B : CurrentSource M) where
  sort : A.pair.base.Sorts
  point : A.pair.base.Point sort
  atom : A.pair.base.source.Atom sort sort
  parity : PairSafeSplit.Full.ParityGateData A.pair.base.source A.pair.base.homogeneous atom point
  target : B = SingleStep.successor A (parity.phase A.pair.base.cco)

namespace SelectedStep
variable {A B : CurrentSource M} (s : SelectedStep A B)

abbrev phase := s.parity.phase A.pair.base.cco
abbrev child := SingleStep.pairChild A s.phase

def pairStep : PairSafeSplit.Terminal.SelectedStep A.pair s.child :=
  ⟨s.sort,s.point,s.atom,s.parity,rfl⟩

theorem potential_lt (step : SelectedStep A B) : B.potential < A.potential := by
  rw [step.target]
  exact SingleStep.potential_lt A step.phase

def reduct : FullReduct A.table B.table :=
  Eq.mp (congrArg (fun C : CurrentSource M => FullReduct A.table C.table) s.target.symm)
    (SingleStep.reduct A s.phase)

def transition : UnaryTransition A.finiteAge B.finiteAge := s.reduct.transition A.homogeneous

theorem language_size (step : SelectedStep A B) : B.language.size = A.language.size+1 := by
  rw [step.target]
  rfl

end SelectedStep

abbrev Next (A B : CurrentSource M) := Nonempty (SelectedStep A B)

/-- Principal progress chooses the actual original B047 parity gate
and builds the full successor. There is NO later-stage provider argument. -/
theorem actual_progress (A : CurrentSource M) (h : A.Obstruction) :
    ∃ B : CurrentSource M, Next A B := by
  obtain ⟨C,⟨s⟩⟩ := PairSafeSplit.Terminal.selected_progress A.pair h
  exact ⟨SingleStep.successor A s.phase,⟨⟨s.sort,s.point,s.atom,s.parity,rfl⟩⟩⟩

end
end CCO.FullPhaseLift.Tower
