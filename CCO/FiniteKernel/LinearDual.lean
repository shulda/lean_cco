import CCO.FiniteKernel.DirectSumDual
import CCO.FiniteKernel.CountableSeparation
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Data.DFinsupp.Encodable

/-! The actual full-product annihilator of finite-support tests and the
double-annihilator identity. Separation is the explicit countable extension
already proved in this package; the representing tuple is a FULL product.
-/

universe u v w
namespace CCO.FiniteKernel
noncomputable section
open scoped DirectSum
variable (K : Type u) [Field K] {I : Type v} (V : I → Type w) [DecidableEq I]
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

def evaluation : (∀ i, V i) →ₗ[K] Module.Dual K (TestSpace K V) where
  toFun := evalTuple K V
  map_add' x y := by
    apply DirectSum.linearMap_ext
    intro i
    ext phi
    simp only [LinearMap.comp_apply,LinearMap.add_apply,evalTuple,productEvaluation_lof,Pi.add_apply,map_add]
  map_smul' a x := by
    apply DirectSum.linearMap_ext
    intro i
    ext phi
    simp only [LinearMap.comp_apply,LinearMap.smul_apply,evalTuple,productEvaluation_lof,Pi.smul_apply,map_smul,RingHom.id_apply]

def testEvaluation : TestSpace K V →ₗ[K] Module.Dual K (∀ i, V i) :=
  (evaluation K V).flip

def perp (R : Submodule K (TestSpace K V)) : Submodule K (∀ i, V i) :=
  R.dualAnnihilator.comap (evaluation K V)

def ann (N : Submodule K (∀ i, V i)) : Submodule K (TestSpace K V) :=
  N.dualAnnihilator.comap (testEvaluation K V)

@[simp] theorem mem_perp (R : Submodule K (TestSpace K V)) (x : ∀ i,V i) :
    x ∈ perp K V R ↔ ∀ ell ∈ R, evalTuple K V x ell = 0 := by
  change evaluation K V x ∈ R.dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  rfl

@[simp] theorem mem_ann (N : Submodule K (∀ i,V i)) (ell : TestSpace K V) :
    ell ∈ ann K V N ↔ ∀ x ∈ N, evalTuple K V x ell = 0 := by
  change testEvaluation K V ell ∈ N.dualAnnihilator ↔ _
  rw [Submodule.mem_dualAnnihilator]
  rfl

variable [∀ i, FiniteDimensional K (V i)] [Countable (TestSpace K V)]

theorem ann_perp (R : Submodule K (TestSpace K V)) : ann K V (perp K V R) = R := by
  ext ell
  constructor
  · intro h
    by_contra hell
    obtain ⟨f,hR,h1⟩ := exists_countable_separating_form K (TestSpace K V) R ell hell
    obtain ⟨x,hx,_⟩ := exists_unique_evalTuple K V f
    rw [hx] at hR h1
    have hxR : x ∈ perp K V R := (mem_perp K V R x).mpr hR
    have hz := (mem_ann K V _ ell).mp h x hxR
    rw [h1] at hz
    exact one_ne_zero hz
  · intro hell
    apply (mem_ann K V _ ell).mpr
    intro x hx
    exact (mem_perp K V R x).mp hx ell hell

theorem perp_injective : Function.Injective (perp K V) := by
  intro R R' h
  have hh := congrArg (ann K V) h
  simpa only [ann_perp] using hh

theorem test_countable [Countable I] [∀ i, Countable (Module.Dual K (V i))] :
    Countable (TestSpace K V) := inferInstance

end
end CCO.FiniteKernel
