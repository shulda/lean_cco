import CCO.QuotientTransport.SharedActions.PointLifting
import CCO.QuotientTransport.SharedActions.Orbitals
import Mathlib.Algebra.Group.PUnit

/-! Actual B040 action boundaries C48/C49. These expose why equality is
retained during saturation and why nonempty/onto/fibre premises matter. -/

namespace CCO.QuotientTransport.SharedActions

open GroupActions

section Saturation

variable {A : Type*}

def unitProjection (_ : A) : PUnit := PUnit.unit

/-- Constant maps have universal saturation whenever the FULL relation is nonempty. -/
theorem constant_saturation_all (O : A → A → Prop)
    (nonempty : ∃ a b, O a b) :
    saturation (unitProjection : A → PUnit) unitProjection O = (fun _ _ => True) := by
  funext x y
  apply propext
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨a, b, h⟩ := nonempty
    exact ⟨a, b, rfl, h, rfl⟩

/-- Removing equality BEFORE saturation can erase a full diagonal orbital. -/
theorem diagonal_prefilter_loses_everything (O : A → A → Prop)
    (diagonal : ∀ x y, O x y → x = y) (x y : A) :
    ¬ saturation (unitProjection : A → PUnit) unitProjection
      (fun u v => O u v ∧ u ≠ v) x y := by
  rintro ⟨u, v, _, ⟨h, different⟩, _⟩
  exact different (diagonal u v h)

variable {G : Type*} [Group G] [MulAction G A]

/-- C48 first half: an ACTUAL diagonal orbital saturates to diverse pairs. -/
theorem diagonal_orbital_saturation_boundary (a b : A) (different : a ≠ b) :
    a ≠ b ∧
    saturation (unitProjection : A → PUnit) unitProjection (orbital (G := G) a a) a b ∧
    ¬ saturation (unitProjection : A → PUnit) unitProjection
      (fun u v => orbital (G := G) a a u v ∧ u ≠ v) a b := by
  refine ⟨different, ?_, ?_⟩
  · exact ⟨a, a, rfl, orbital_nonempty a a, rfl⟩
  · exact diagonal_prefilter_loses_everything _ (by
      rintro x y ⟨g, hx, hy⟩
      exact hx.symm.trans hy) a b

/-- C48 second half: an ACTUAL off-diagonal orbital saturates back to equality. -/
theorem diversity_orbital_saturates_diagonal (a b : A) (different : a ≠ b) :
    (∀ x y, orbital (G := G) a b x y → x ≠ y) ∧
    saturation (unitProjection : A → PUnit) unitProjection (orbital (G := G) a b) a a := by
  constructor
  · rintro x y ⟨g, hx, hy⟩ equal
    exact different (smul_left_cancel g (hx.trans (equal.trans hy.symm)))
  · exact ⟨a, b, rfl, orbital_nonempty a b, rfl⟩

end Saturation

namespace PointHypotheses

open NonfaithfulNonsplit

local instance {H : Type*} [Group H] : MulAction H Empty where
  smul _ x := nomatch x
  one_smul x := nomatch x
  mul_smul _ _ x := nomatch x

local instance {H : Type*} [Group H] : MulAction H PUnit where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

local instance {H : Type*} [Group H] : MulAction H Bool where
  smul _ x := x
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

def trivialMap : C4 →* C2 := 1

theorem trivialMap_not_onto : ¬ Function.Surjective trivialMap := by
  intro onto
  obtain ⟨k, hk⟩ := onto nontrivial
  exact nontrivial_ne_one hk.symm

def emptyProjection : Empty → Empty := id

theorem empty_projection_equivariant (k : C4) (x : Empty) :
    emptyProjection (k • x) = trivialMap k • emptyProjection x := by cases x

/-- Empty Y=B makes EVERY request vacuous, although the group map is not onto. -/
theorem empty_domain_requests :
    Function.Surjective emptyProjection ∧
    GroupActions.PrescribedLift trivialMap emptyProjection ∧
    ¬ Function.Surjective trivialMap := by
  refine ⟨?_, ?_, trivialMap_not_onto⟩
  · intro x; cases x
  · intro x; cases x

def missingProjection (_ : PUnit) : C2 := 1

theorem missing_projection_equivariant (k : C4) (x : PUnit) :
    missingProjection (k • x) = trivialMap k • missingProjection x := by
  change (1 : C2) = 1 * 1
  rw [one_mul]

/-- With π not onto, compatibility tests only the identity target element. -/
theorem nononto_point_map_requests :
    ¬ Function.Surjective missingProjection ∧
    GroupActions.PrescribedLift trivialMap missingProjection ∧
    ¬ Function.Surjective trivialMap := by
  refine ⟨?_, ?_, trivialMap_not_onto⟩
  · intro onto
    obtain ⟨x, hx⟩ := onto nontrivial
    exact nontrivial_ne_one hx.symm
  · intro x y γ compatible
    have gamma_one : γ = 1 := by
      change γ * 1 = 1 at compatible
      simpa only [mul_one] using compatible
    exact ⟨1, gamma_one.symm, Subsingleton.elim _ _⟩

def sheetProjection (_ : Bool) : PUnit := PUnit.unit

theorem sheet_projection_equivariant (k : C2) (x : Bool) :
    sheetProjection (k • x) = (MonoidHom.id C2) k • sheetProjection x := rfl

/-- Onto rho alone cannot move between two trivial-action sheets of a fibre. -/
theorem onto_without_kernel_transitivity :
    Function.Surjective (MonoidHom.id C2) ∧
    Function.Surjective sheetProjection ∧
    ¬ GroupActions.FibreTransitive (MonoidHom.id C2) sheetProjection ∧
    ¬ GroupActions.PrescribedLift (MonoidHom.id C2) sheetProjection := by
  refine ⟨fun γ => ⟨γ, rfl⟩, fun x => ⟨false, Subsingleton.elim _ _⟩, ?_, ?_⟩
  · intro fibres
    obtain ⟨k, _, impossible⟩ := fibres false true rfl
    change false = true at impossible
    cases impossible
  · intro requests
    obtain ⟨k, _, impossible⟩ := requests false true 1 rfl
    change false = true at impossible
    cases impossible

/-- With a nonfaithful TARGET action, lifting the induced point permutation
is strictly weaker than lifting the specified GROUP ELEMENT. -/
theorem point_motion_does_not_prescribe_group_element :
    (∀ x y : PUnit, ∀ γ : C2, γ • x = y → ∃ k : C4, k • x = y) ∧
    ¬ GroupActions.PrescribedLift trivialMap (id : PUnit → PUnit) := by
  constructor
  · intro x y γ _
    exact ⟨1, Subsingleton.elim _ _⟩
  · intro requests
    obtain ⟨k, image, _⟩ := requests PUnit.unit PUnit.unit nontrivial rfl
    exact nontrivial_ne_one image.symm

end PointHypotheses
end CCO.QuotientTransport.SharedActions
