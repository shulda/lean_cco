import CCO.FiniteKernel.DirectSumDual
import Mathlib.LinearAlgebra.Pi

/-! Literal finite-coordinate zero extensions, with their evaluation identity.
No finite-dimensionality/countability/actual-group premise is needed here. -/

universe u v w
namespace CCO.FiniteKernel
open scoped DirectSum

variable (K : Type u) [Field K] {I : Type v} [DecidableEq I] (V : I → Type w)
variable [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

abbrev FiniteProduct (A : Finset I) := ∀ i : ↥A, V i.val

def restrictVec (A : Finset I) : (∀ i, V i) →ₗ[K] FiniteProduct V A where
  toFun x i := x i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def extendVec (A : Finset I) : FiniteProduct V A →ₗ[K] (∀ i, V i) where
  toFun x i := if h : i ∈ A then x ⟨i,h⟩ else 0
  map_add' := by intro x y; funext i; split_ifs with h <;> simp [h]
  map_smul' := by intro c x; funext i; split_ifs with h <;> simp [h]

@[simp] theorem restrict_extend (A : Finset I) (x : FiniteProduct V A) :
    restrictVec K V A (extendVec K V A x) = x := by
  funext i
  simp [restrictVec,extendVec,i.property]

def restrictBetween {A B : Finset I} (hAB : A ⊆ B) :
    FiniteProduct V B →ₗ[K] FiniteProduct V A where
  toFun x i := x ⟨i.val,hAB i.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem restrictBetween_restrictVec {A B : Finset I} (hAB : A ⊆ B) (x : ∀ i, V i) :
    restrictBetween K V hAB (restrictVec K V B x) = restrictVec K V A x := rfl

@[simp] theorem restrictBetween_extendVec {A B : Finset I} (hAB : A ⊆ B)
    (x : FiniteProduct V A) :
    restrictBetween K V hAB (restrictVec K V B (extendVec K V A x)) = x := by
  rw [restrictBetween_restrictVec,restrict_extend]

@[simp] theorem restrictVec_extendVec_of_subset {A B : Finset I} (hAB : A ⊆ B)
    (x : FiniteProduct V B) :
    restrictVec K V A (extendVec K V B x) = restrictBetween K V hAB x := by
  funext i
  simp [restrictVec,extendVec,restrictBetween,hAB i.property]

noncomputable def extendForm (A : Finset I) :
    Module.Dual K (FiniteProduct V A) →ₗ[K] TestSpace K V where
  toFun phi := ∑ i : ↥A, DirectSum.lof K I (fun i => Module.Dual K (V i)) i.val
    (phi.comp (LinearMap.single K (fun i : ↥A => V i.val) i))
  map_add' := by
    intro phi psi
    simp only [LinearMap.add_comp,map_add,Finset.sum_add_distrib]
  map_smul' := by
    intro c phi
    simp only [LinearMap.smul_comp,map_smul,Finset.smul_sum,RingHom.id_apply]

theorem evalTuple_extendForm (A : Finset I) (x : ∀ i, V i)
    (phi : Module.Dual K (FiniteProduct V A)) :
    evalTuple K V x (extendForm K V A phi) = phi (restrictVec K V A x) := by
  classical
  change productEvaluation K V x (∑ i : ↥A,
    DirectSum.lof K I (fun i => Module.Dual K (V i)) i.val
      (phi.comp (LinearMap.single K (fun i : ↥A => V i.val) i))) = _
  simp only [map_sum,productEvaluation_lof,LinearMap.comp_apply]
  rw [← map_sum]
  congr 1
  ext j
  simp [LinearMap.single_apply,restrictVec]

theorem extendForm_injective (A : Finset I) : Function.Injective (extendForm K V A) := by
  intro phi psi he
  apply LinearMap.ext
  intro x
  have hh := congrArg (fun d => evalTuple K V (extendVec K V A x) d) he
  simpa only [evalTuple_extendForm,restrict_extend] using hh

theorem evalTuple_single (j : I) (x : V j) (d : TestSpace K V) :
    evalTuple K V (LinearMap.single K V j x) d =
      (DirectSum.component K I (fun i => Module.Dual K (V i)) j d) x := by
  have hh : productEvaluation K V (LinearMap.single K V j x) =
      (Module.Dual.eval K (V j) x).comp (DirectSum.component K I (fun i => Module.Dual K (V i)) j) := by
    apply DirectSum.linearMap_ext
    intro i
    apply LinearMap.ext
    intro phi
    by_cases hi : i = j
    · subst i
      simp [productEvaluation_lof,LinearMap.comp_apply,LinearMap.single_apply]
    · simp [productEvaluation_lof,LinearMap.comp_apply,LinearMap.single_apply,
        DirectSum.component.of,hi,Ne.symm hi]
  exact congrArg (fun f : TestSpace K V →ₗ[K] K => f d) hh

theorem test_ext {d e : TestSpace K V}
    (h : ∀ x : (∀ i, V i), evalTuple K V x d = evalTuple K V x e) : d = e := by
  apply DirectSum.ext_component K
  intro i
  apply LinearMap.ext
  intro x
  simpa only [evalTuple_single] using h (LinearMap.single K V i x)

theorem extendForm_between {A B : Finset I} (hAB : A ⊆ B)
    (phi : Module.Dual K (FiniteProduct V A)) :
    extendForm K V A phi = extendForm K V B (phi.comp (restrictBetween K V hAB)) := by
  apply test_ext K V
  intro x
  simp only [evalTuple_extendForm,LinearMap.comp_apply,restrictBetween_restrictVec]

noncomputable def restrictedTestSpace (A : Finset I) : Submodule K (TestSpace K V) :=
  LinearMap.range (extendForm K V A)

theorem restrictedTestSpace_mono {A B : Finset I} (hAB : A ⊆ B) :
    restrictedTestSpace K V A ≤ restrictedTestSpace K V B := by
  rintro d ⟨phi,rfl⟩
  exact ⟨phi.comp (restrictBetween K V hAB), (extendForm_between K V hAB phi).symm⟩

theorem eval_extendForm (A : Finset I) (x : ∀ i, V i)
    (phi : Module.Dual K (FiniteProduct V A)) :
    evalTuple K V x (extendForm K V A phi) = phi (restrictVec K V A x) :=
  evalTuple_extendForm K V A x phi

@[simp] theorem restrict_extendVec (A : Finset I) (x : FiniteProduct V A) :
    restrictVec K V A (extendVec K V A x) = x := restrict_extend K V A x

end CCO.FiniteKernel
