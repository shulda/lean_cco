import CCO.GroupActions
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Hom
import Mathlib.Algebra.Group.TypeTags.Finite

/-! The regular C4 action over its C2 quotient satisfies every prescribed
point lift and has fibre-transitive kernel, yet the group quotient does
not split. This is a directed action control, not a symmetric CCO source. -/
namespace CCO.Owners.Product.Controls.NoSection

abbrev C4 := Multiplicative (ZMod 4)
abbrev C2 := Multiplicative (ZMod 2)

def reduction : ZMod 4 →+ ZMod 2 := (ZMod.castHom (by decide : 2 ∣ 4) (ZMod 2)).toAddMonoidHom

def rho : C4 →* C2 := reduction.toMultiplicative

theorem rho_surjective : Function.Surjective rho := by
  intro b
  obtain ⟨a,ha⟩ := ZMod.castHom_surjective (by decide : 2 ∣ 4) b.toAdd
  exact ⟨Multiplicative.ofAdd a,congrArg Multiplicative.ofAdd ha⟩

theorem equivariant (g x : C4) : rho (g • x) = rho g • rho x := rho.map_mul g x

/-- The lift is chosen for EACH point request; it need not be a homomorphism
of the prescribed quotient element. -/
theorem point_lifts : GroupActions.PrescribedLift rho rho := by
  intro x y γ h
  change γ * rho x = rho y at h
  refine ⟨y*x⁻¹,?_,?_⟩
  · rw [map_mul,map_inv,←h,mul_assoc,mul_inv_cancel,mul_one]
  · change (y*x⁻¹)*x=y
    exact inv_mul_cancel_right y x

theorem onto_fibre_kernel :
    Function.Surjective rho ∧ GroupActions.FibreTransitive rho rho :=
  (GroupActions.prescribed_action_point_lifting rho rho rho_surjective equivariant).mpr point_lifts

/-- An order-at-most-two element of C4 has trivial C2 image. This finite
calculation is about ELEMENTS, not an enumeration of candidate sections. -/
theorem order_two_image : ∀ x : C4, x*x=1 → rho x=1 := by decide

def nontrivial : C2 := Multiplicative.ofAdd 1

theorem nontrivial_sq : nontrivial*nontrivial=1 := by decide

theorem nontrivial_ne_one : nontrivial ≠ 1 := by decide

/-- ALL homomorphic sections are excluded by the image of the C2 generator. -/
theorem no_homomorphic_section : ¬ ∃ s : C2 →* C4, rho.comp s = MonoidHom.id C2 := by
  rintro ⟨s,hs⟩
  have hsq : s nontrivial*s nontrivial=1 := by
    rw [←map_mul,nontrivial_sq,map_one]
  have hzero := order_two_image (s nontrivial) hsq
  have hsplit : rho (s nontrivial) = nontrivial :=
    congrArg (fun f : C2 →* C2 => f nontrivial) hs
  exact nontrivial_ne_one (hsplit.symm.trans hzero)

end CCO.Owners.Product.Controls.NoSection
