import CCO.Owners.Product.Matching
import CCO.FiniteKernel.BinarySource
import Mathlib.Algebra.Group.Action.End

/-! C25: the empty quotient system is handled directly. In particular,
vacuous point requests on an empty carrier are never used to infer a
surjective group map through the nonempty point-lifting criterion. -/
namespace CCO.Owners.Product
open CCO.FiniteKernel

variable {D C O T U V : Type*}

/-- Empty C and surjective C->O force all quotient carriers empty. -/
theorem empty_quotient_system (πD : D → O) (πC : C → O) (t : D → T)
    (surjC : Function.Surjective πC) (surjT : Function.Surjective t) [IsEmpty C] :
    IsEmpty O ∧ IsEmpty D ∧ IsEmpty T ∧ IsEmpty (Pullback πD πC) := by
  have emptyO : IsEmpty O := ⟨fun o => by
    obtain ⟨c,_⟩ := surjC o
    exact isEmptyElim c⟩
  have emptyD : IsEmpty D := ⟨fun d => emptyO.false (πD d)⟩
  have emptyT : IsEmpty T := ⟨fun u => by
    obtain ⟨d,_⟩ := surjT u
    exact emptyD.false d⟩
  exact ⟨emptyO,emptyD,emptyT,⟨fun w => isEmptyElim w.val.2⟩⟩

theorem empty_nested_product (πC : C → O) (s : T → O) [IsEmpty C] :
    IsEmpty (Pullback s πC) := ⟨fun w => isEmptyElim w.val.2⟩

/-- This is the FULL structural automorphism group, not an arbitrary
abstract acting group over an empty set. -/
theorem empty_actual_aut_subsingleton [IsEmpty U] (S : BinaryStructure U) :
    Subsingleton S.Aut := by
  refine ⟨fun g h => Subtype.ext (Equiv.ext (fun x => isEmptyElim x))⟩

/-- Both actual groups are the unique one-element groups. The source
identity witnesses surjectivity of every displayed induced group map. -/
theorem empty_actual_aut_hom_surjective [IsEmpty U] [IsEmpty V]
    (S : BinaryStructure U) (R : BinaryStructure V) (ρ : S.Aut →* R.Aut) :
    Function.Surjective ρ := by
  letI := empty_actual_aut_subsingleton R
  intro g
  exact ⟨1,Subsingleton.elim _ _⟩

theorem empty_actual_aut_unique [IsEmpty U] (S : BinaryStructure U) (g : S.Aut) :
    g = 1 := by
  letI := empty_actual_aut_subsingleton S
  exact Subsingleton.elim _ _

/-- Only the fibre assertion itself is vacuous, independently of groups. -/
theorem empty_fibre_transitive {GW GT : Type*} [Group GW] [Group GT]
    [MulAction GW U] [MulAction GT V] [IsEmpty U]
    (ρ : GW →* GT) (π : U → V) : GroupActions.FibreTransitive ρ π := by
  intro x
  exact isEmptyElim x

theorem empty_point_requests {GW GT : Type*} [Group GW] [Group GT]
    [MulAction GW U] [MulAction GT V] [IsEmpty U]
    (ρ : GW →* GT) (π : U → V) : GroupActions.PrescribedLift ρ π := by
  intro x
  exact isEmptyElim x

/-- The actual empty-system action conclusion combines a genuine trivial
TARGET group with the separately vacuous fibre statement. -/
theorem empty_actual_action_result [IsEmpty U] [IsEmpty V]
    (S : BinaryStructure U) (R : BinaryStructure V) (ρ : S.Aut →* R.Aut)
    (π : U → V) :
    Function.Surjective ρ ∧ GroupActions.FibreTransitive ρ π :=
  ⟨empty_actual_aut_hom_surjective S R ρ,empty_fibre_transitive ρ π⟩

end CCO.Owners.Product
