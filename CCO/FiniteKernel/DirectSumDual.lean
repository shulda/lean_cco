import CCO.FiniteKernel.FiniteBidual
import Mathlib.Algebra.DirectSum.Module

/-!
# The dual of finite-support coordinate tests is the FULL product

Restrict an actual linear form to each coordinate, apply the explicitly proved
finite bidual sum, and glue the evaluations using the direct-sum universal
property. The representing tuple has NO support restriction. There is no
countability or nonempty-family premise, and zero-dimensional factors work.
-/

universe u v w
namespace CCO.FiniteKernel

open scoped DirectSum

variable (K : Type u) [Field K] {I : Type v} (V : I → Type w)
variable [DecidableEq I]
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

abbrev FiniteSupportTests := ⨁ i, Module.Dual K (V i)

noncomputable def productEvaluation (x : ∀ i, V i) : FiniteSupportTests K V →ₗ[K] K :=
  DirectSum.toModule K I K (fun i => Module.Dual.eval K (V i) (x i))

@[simp] theorem productEvaluation_lof (x : ∀ i, V i) (i : I) (phi : Module.Dual K (V i)) :
    productEvaluation K V x (DirectSum.lof K I (fun i => Module.Dual K (V i)) i phi) =
      phi (x i) := by
  simp only [productEvaluation,DirectSum.toModule_lof,Module.Dual.eval_apply]

variable [∀ i, FiniteDimensional K (V i)]

/-- Every linear form on all finite-support tests is evaluation at one UNIQUE
full product tuple. Each coordinate vector is obtained by the finite basis sum.
-/
theorem existsUnique_product_representation (f : FiniteSupportTests K V →ₗ[K] K) :
    ∃! x : (∀ i, V i), f = productEvaluation K V x := by
  classical
  have hcoord (i : I) : ∃ x : V i, ∀ phi : Module.Dual K (V i),
      f (DirectSum.lof K I (fun i => Module.Dual K (V i)) i phi) = phi x := by
    obtain ⟨x,hx,_⟩ := existsUnique_bidual_vector K (V i)
      (f.comp (DirectSum.lof K I (fun i => Module.Dual K (V i)) i))
    exact ⟨x,hx⟩
  choose x hx using hcoord
  have hrepr : f = productEvaluation K V x := by
    apply DirectSum.linearMap_ext
    intro i
    ext phi
    exact (hx i phi).trans (productEvaluation_lof K V x i phi).symm
  refine ⟨x,hrepr,?_⟩
  intro y hy
  funext i
  apply dual_values_determine_vector K (V i) (Module.finBasis K (V i))
  intro phi
  have hh := congrArg (fun g : FiniteSupportTests K V →ₗ[K] K =>
    g (DirectSum.lof K I (fun i => Module.Dual K (V i)) i phi)) (hy.symm.trans hrepr)
  simpa only [productEvaluation_lof] using hh

theorem productEvaluation_injective : Function.Injective (productEvaluation K V) := by
  intro x y h
  funext i
  apply dual_values_determine_vector K (V i) (Module.finBasis K (V i))
  intro phi
  have hh := congrArg (fun g : FiniteSupportTests K V →ₗ[K] K =>
    g (DirectSum.lof K I (fun i => Module.Dual K (V i)) i phi)) h
  simpa only [productEvaluation_lof] using hh

theorem productEvaluation_surjective : Function.Surjective (productEvaluation K V) := by
  intro f
  obtain ⟨x,hx,_⟩ := existsUnique_product_representation K V f
  exact ⟨x,hx.symm⟩

/-- Source-facing names for the actual test space and FULL tuple evaluation. -/
abbrev TestSpace := FiniteSupportTests K V

noncomputable abbrev evalTuple (x : ∀ i, V i) : TestSpace K V →ₗ[K] K :=
  productEvaluation K V x

@[simp] theorem evalTuple_lof (x : ∀ i, V i) (i : I) (phi : Module.Dual K (V i)) :
    evalTuple K V x (DirectSum.lof K I (fun i => Module.Dual K (V i)) i phi) = phi (x i) :=
  productEvaluation_lof K V x i phi

theorem exists_unique_evalTuple (f : TestSpace K V →ₗ[K] K) :
    ∃! x : (∀ i, V i), f = evalTuple K V x := existsUnique_product_representation K V f

end CCO.FiniteKernel
