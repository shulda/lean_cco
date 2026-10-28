import CCO.FiniteKernel.BinarySource
import Mathlib.Algebra.Group.Equiv.Basic

/-! The complete original right-difference binary language of an arbitrary
group. Its FULL automorphisms are left translations and it is homogeneous.
This elementary source is directed; no symmetric AtomicSource is substituted. -/

universe u
namespace CCO.FiniteKernel.Countercontrols.RightRegular

variable (K : Type u) [Group K]

def source : BinaryStructure K where
  Unary := Empty
  Binary := K
  unary r := r.elim
  binary r x y := y = x * r

def leftPerm (t : K) : Equiv.Perm K where
  toFun x := t * x
  invFun x := t⁻¹ * x
  left_inv x := inv_mul_cancel_left t x
  right_inv x := mul_inv_cancel_left t x

def leftAut (t : K) : (source K).Aut := ⟨leftPerm K t,by
  constructor
  · intro r
    exact r.elim
  · intro r x y
    change K at r
    change t * y = (t * x) * r ↔ y = x * r
    rw [mul_assoc]
    exact mul_left_cancel_iff⟩

/-- FULL automorphism classification, from the named orbital based at 1. -/
theorem fullAut_left (g : (source K).Aut) (x : K) : g.val x = g.val 1 * x := by
  have hx := (BinaryStructure.Aut.binary (source K) g x 1 x).mpr
    (show x = (1 : K) * x from (one_mul x).symm)
  exact hx

theorem leftAut_injective : Function.Injective (leftAut K) := by
  intro s t h
  have hh := congrArg (fun g : (source K).Aut => g.val 1) h
  change s * 1 = t * 1 at hh
  simpa only [mul_one] using hh

theorem leftAut_surjective : Function.Surjective (leftAut K) := by
  intro g
  refine ⟨g.val 1,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  exact fun x => (fullAut_left K g x).symm

noncomputable def fullAutEquiv : K ≃ (source K).Aut :=
  Equiv.ofBijective (leftAut K) ⟨leftAut_injective K,leftAut_surjective K⟩

def leftHom : K →* (source K).Aut where
  toFun := leftAut K
  map_one' := by
    apply Subtype.ext
    apply Equiv.ext
    exact one_mul
  map_mul' s t := by
    apply Subtype.ext
    apply Equiv.ext
    exact mul_assoc s t

noncomputable def fullAutMulEquiv : K ≃* (source K).Aut :=
  MulEquiv.ofBijective (leftHom K) ⟨leftAut_injective K,leftAut_surjective K⟩

theorem homogeneous : (source K).Homogeneous := by
  intro A f _ _ hb
  classical
  by_cases hA : A.Nonempty
  · obtain ⟨x,hx⟩ := hA
    let x₀ : ↥A := ⟨x,hx⟩
    refine ⟨leftAut K (f x₀ * x⁻¹),?_⟩
    intro y
    have hh := (hb (x⁻¹ * y.val) x₀ y).mpr
      (show y.val = x * (x⁻¹ * y.val) from (mul_inv_cancel_left x y.val).symm)
    change (f x₀ * x⁻¹) * y.val = f y
    exact (mul_assoc _ _ _).trans hh.symm
  · refine ⟨1,?_⟩
    intro x
    exact False.elim (hA ⟨x.val,x.property⟩)

end CCO.FiniteKernel.Countercontrols.RightRegular
