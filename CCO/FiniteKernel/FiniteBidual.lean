import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Finite biduality by the explicit basis sum

For a finite basis `b`, the representing vector of `L` is literally
`∑ i, L (b.coord i) • b i`. The proof expands each old linear form in these
coordinate forms. No bidual surjectivity or separation theorem is invoked.
-/

universe u v w
namespace CCO.FiniteKernel

open Module

variable (K : Type u) [Field K] (V : Type v) [AddCommGroup V] [Module K V]

noncomputable def vectorOfDualForm {I : Type w} [Fintype I] (b : Basis I K V)
    (L : Module.Dual K (Module.Dual K V)) : V :=
  ∑ i, L (b.coord i) • b i

theorem coordinate_form_expansion {I : Type w} [Fintype I] (b : Basis I K V)
    (phi : Module.Dual K V) :
    ∑ i, phi (b i) • b.coord i = phi := by
  classical
  ext x
  simp only [LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  change (∑ i, phi (b i) * b.repr x i) = phi x
  calc
    _ = ∑ i, b.repr x i * phi (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = phi (∑ i, b.repr x i • b i) := by simp only [map_sum,map_smul,smul_eq_mul]
    _ = phi x := by rw [b.sum_repr]

theorem vectorOfDualForm_spec {I : Type w} [Fintype I] (b : Basis I K V)
    (L : Module.Dual K (Module.Dual K V)) (phi : Module.Dual K V) :
    L phi = phi (vectorOfDualForm K V b L) := by
  classical
  symm
  unfold vectorOfDualForm
  calc
    _ = ∑ i, L (b.coord i) * phi (b i) := by simp only [map_sum,map_smul,smul_eq_mul]
    _ = ∑ i, phi (b i) * L (b.coord i) := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_comm _ _
    _ = L (∑ i, phi (b i) • b.coord i) := by simp only [map_sum,map_smul,smul_eq_mul]
    _ = L phi := by rw [coordinate_form_expansion K V b phi]

theorem dual_values_determine_vector {I : Type w} [Fintype I] (b : Basis I K V)
    {x y : V} (h : ∀ phi : Module.Dual K V, phi x = phi y) : x = y := by
  apply b.repr.injective
  ext i
  exact h (b.coord i)

theorem existsUnique_bidual_vector_of_basis {I : Type w} [Fintype I] (b : Basis I K V)
    (L : Module.Dual K (Module.Dual K V)) :
    ∃! x : V, ∀ phi : Module.Dual K V, L phi = phi x := by
  refine ⟨vectorOfDualForm K V b L, vectorOfDualForm_spec K V b L, ?_⟩
  intro y hy
  apply dual_values_determine_vector K V b
  intro phi
  exact (hy phi).symm.trans (vectorOfDualForm_spec K V b L phi)

theorem existsUnique_bidual_vector [FiniteDimensional K V]
    (L : Module.Dual K (Module.Dual K V)) :
    ∃! x : V, ∀ phi : Module.Dual K V, L phi = phi x :=
  existsUnique_bidual_vector_of_basis K V (Module.finBasis K V) L

end CCO.FiniteKernel
