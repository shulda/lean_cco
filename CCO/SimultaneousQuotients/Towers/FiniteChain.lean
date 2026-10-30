import CCO.SimultaneousQuotients.Towers.Flattening

/-! Every finite chain of ACTUAL current quotient sets flattens canonically.
The chain syntax never replaces a quotient by chosen representative points.
Exactness is handled separately by safe upward pullback at each source step. -/

universe v
namespace CCO.SimultaneousQuotients.Towers

/-- A finite sequence of current-stage setoid quotients, with zero steps. -/
inductive Chain : (A : Type v) → Type (v + 1) where
  | nil (A : Type v) : Chain A
  | cons {A : Type v} (J : Setoid A) (tail : Chain (Quotient J)) : Chain A

namespace Chain

variable {A : Type v}

def length : {A : Type v} → Chain A → Nat
  | _, .nil _ => 0
  | _, .cons _ tail => tail.length + 1

def Carrier : {A : Type v} → Chain A → Type v
  | A, .nil _ => A
  | _, .cons _ tail => tail.Carrier

def project : {A : Type v} → (C : Chain A) → A → C.Carrier
  | _, .nil _, x => x
  | _, .cons _ tail, x => tail.project (Quotient.mk'' x)

theorem project_surjective (C : Chain A) : Function.Surjective C.project := by
  induction C with
  | nil A => exact Function.surjective_id
  | @cons A J tail ih =>
    exact ih.comp Quotient.mk''_surjective

/-- The one total initial kernel determined by the entire current tower. -/
def kernel (C : Chain A) : Setoid A := Setoid.ker C.project

noncomputable def flatten (C : Chain A) : C.Carrier ≃ Quotient C.kernel :=
  (Setoid.quotientKerEquivOfSurjective C.project (C.project_surjective)).symm

@[simp] theorem flatten_project (C : Chain A) (x : A) :
    C.flatten (C.project x) = (Quotient.mk'' x : Quotient C.kernel) := by
  apply (C.flatten).symm.injective
  rw [Equiv.symm_apply_apply]
  rfl

/-- Zero-stage tower: original carrier and identity projection. -/
theorem zero_project : (Chain.nil A).project = id := rfl

theorem zero_kernel : (Chain.nil A).kernel = ⊥ := by
  apply Setoid.ext
  intro x y
  rfl

/-- At each new step, the total kernel is the SAFE pullback of the
remaining current-stage kernel. No reverse exact descent is asserted. -/
theorem cons_kernel (J : Setoid A) (tail : Chain (Quotient J)) :
    (Chain.cons J tail).kernel = totalKernel J tail.kernel := rfl

theorem step_le_kernel (J : Setoid A) (tail : Chain (Quotient J)) :
    J ≤ (Chain.cons J tail).kernel := original_le_total J tail.kernel

/-- The flattened final class is determined by, and determines, equality
at the genuine last quotient stage. -/
theorem project_eq_iff (C : Chain A) (x y : A) :
    C.project x = C.project y ↔ C.kernel x y := Iff.rfl

end Chain
end CCO.SimultaneousQuotients.Towers
