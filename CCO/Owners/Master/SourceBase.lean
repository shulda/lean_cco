import CCO.Owners.Master.StageData
import CCO.Owners.Master.DiagramBoundary
import Mathlib.Algebra.Group.Action.End

/-! The actual top-equivalence quotient supplies every initial decoration.
A bare singleton set is not used to assert closure in an unrelated ambient
packet structure: the AMBIENT quotient itself is proved a singleton. -/

universe v w t z
namespace CCO.Owners.Master
noncomputable section
open RawExact ExactCRT Provider Product

variable {A : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => A))
variable {G : Type t} [Group G] [MulAction G A] [Countable A]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)

instance emptyCoordinateSubsingleton : Subsingleton (Coordinate S H cco ∅) := by
  constructor
  intro x y
  induction x using Quotient.inductionOn with
  | _ a =>
    induction y using Quotient.inductionOn with
    | _ b =>
      apply Quotient.sound
      rw [coordinateKernel_empty S H cco]
      trivial

def initialPoint : Coordinate S H cco ∅ :=
  coordinateProjection S H cco ∅ (Classical.choice (S.nonemptySort ()))

def initialFiniteStage : FiniteStage S H cco ∅ :=
  Diagram.singletonStage (exactAmbient S H cco) IsUpset (initialPoint S H cco)

theorem initial_member (x : Coordinate S H cco ∅) :
    x ∈ (initialFiniteStage S H cco).B ∅ := by
  refine ⟨Finset.Subset.refl ∅,?_⟩
  exact Subsingleton.elim _ _

theorem initialDecorations (T : Set A) :
    Decorations S H cco (initialFiniteStage S H cco) T := by
  constructor
  · intro V _ within x _
    have hV : V = ∅ := Finset.subset_empty.mp within
    subst V
    exact initial_member S H cco x
  · intro V _ within x hx y hxy
    have hV : V = ∅ := Finset.subset_empty.mp within
    subst V
    exact initial_member S H cco y
  · intro V _ within p _ _
    have hV : V = ∅ := Finset.subset_empty.mp within
    subst V
    refine ⟨1,?_⟩
    intro x
    exact Subsingleton.elim _ _
  · intro V W hV hW within hWV
    have eV : V = ∅ := Finset.subset_empty.mp within
    subst V
    have eW : W = ∅ := Finset.subset_empty.mp hWV
    subst W
    constructor
    · intro γ
      refine ⟨1,?_⟩
      exact Subsingleton.elim _ _
    · intro x y _
      exact ⟨1,map_one _,Subsingleton.elim _ _⟩

def initialSourceStage (T : Set A) : SourceStage.{v,w,t,z} S H cco T ∅ where
  finite := initialFiniteStage S H cco
  decorations := initialDecorations S H cco T
  compatible := Diagram.singletonStage_crt (exactAmbient S H cco) IsUpset
    (initialPoint S H cco)

end
end CCO.Owners.Master
