import CCO.RigidGroupoid.Geometry.RootedGroupoid
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Group.TypeTags.Basic

/-! Actual isotropy is a finite group, every element is self-inverse, and its
additive form is a finite F2 vector space. Hom-sets carry both actual endpoint
torsor coordinates. None of this uses a finite-index parity theorem. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

def Isotropy (C : ExactCalculus S) {i : ι} (A : Kernel S i) := Arrow S A A

namespace Isotropy
variable {S} (C : ExactCalculus S) {i : ι} (A : Kernel S i)

instance group : Group (Isotropy S C A) where
  mul R T := Arrow.comp C R T
  one := Arrow.id A
  inv R := Arrow.inv R
  mul_assoc R T U := Arrow.comp_assoc C R T U
  one_mul R := Arrow.id_comp C R
  mul_one R := Arrow.comp_id C R
  inv_mul_cancel R := Arrow.inv_comp C R

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
include H

theorem inverse_self (R : Isotropy S C A) : R⁻¹ = R :=
  Arrow.ext (R.exact.same_sort_converse S H)

theorem square_one (R : Isotropy S C A) : R * R = 1 := by
  calc
    R * R = R⁻¹ * R := congrArg (fun T => T * R) (inverse_self C A H R).symm
    _ = 1 := inv_mul_cancel R

theorem comm (R T : Isotropy S C A) : R * T = T * R := by
  calc
    R * T = (R * T)⁻¹ := (inverse_self C A H _).symm
    _ = T⁻¹ * R⁻¹ := mul_inv_rev R T
    _ = T * R := by rw [inverse_self C A H T,inverse_self C A H R]

@[instance_reducible] def commGroup : CommGroup (Isotropy S C A) where
  __ := group C A
  mul_comm := comm C A H

@[instance_reducible] noncomputable def finiteType : Fintype (Isotropy S C A) := by
  letI : Finite (Isotropy S C A) := by
    unfold Isotropy
    exact arrowFinite S H A A
  exact Fintype.ofFinite _

@[instance_reducible] def vectorSpace :
    letI := commGroup C A H
    Module (ZMod 2) (Additive (Isotropy S C A)) := by
  letI := commGroup C A H
  apply AddCommGroup.zmodModule
  intro x
  change (2 : ℕ) • x = 0
  rw [two_nsmul]
  change (show Isotropy S C A from x) * (show Isotropy S C A from x) = 1
  exact square_one C A H _

end Isotropy

namespace Arrow
variable {S} (C : ExactCalculus S) {i j : ι} {A : Kernel S i} {B : Kernel S j}

/-- The source isotropy coefficient is the UNIQUE arrow translating `T` to
`R`. This is an actual torsor statement, not an assumed abstract action. -/
theorem source_torsor (R T : Arrow S A B) :
    ∃! h : Arrow S A A, h.comp C T = R := by
  refine ⟨R.comp C T.inv, ?_, ?_⟩
  · simp only [comp_assoc,inv_comp,comp_id]
  · intro h hh
    have he := congrArg (fun V => V.comp C T.inv) hh
    simpa only [comp_assoc,comp_inv,comp_id] using he

theorem target_torsor (R T : Arrow S A B) :
    ∃! h : Arrow S B B, T.comp C h = R := by
  refine ⟨T.inv.comp C R, ?_, ?_⟩
  · simp only [← comp_assoc,comp_inv,id_comp]
  · intro h hh
    have he := congrArg (fun V => T.inv.comp C V) hh
    simpa only [← comp_assoc,inv_comp,id_comp] using he

end Arrow
end CCO.RigidGroupoid.Geometry
