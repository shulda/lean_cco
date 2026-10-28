import Mathlib.FieldTheory.Finiteness
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Finite check-map kernel rank counts

The domain is the finite product of the named finite-dimensional F2 motions.
The result counts the finite kernel/IMAGE once the actual source identifies
its image with this kernel; it makes no assertion about the cardinality of
the full possibly infinite automorphism group. Empty families have one motion.
-/

universe u v w z
namespace CCO.FiniteKernel.Named

abbrev F2 := ZMod 2

variable {I : Type u} [Fintype I] (V : I → Type v)
variable [∀ i, AddCommGroup (V i)] [∀ i, Module F2 (V i)]
variable [∀ i, FiniteDimensional F2 (V i)]
variable {Rows : Type w} [AddCommGroup Rows] [Module F2 Rows]

theorem check_kernel_finite (Phi : (∀ i, V i) →ₗ[F2] Rows) : Finite Phi.ker := by
  apply Finite.of_injective (Module.finBasis F2 Phi.ker).equivFun
  exact (Module.finBasis F2 Phi.ker).equivFun.injective

theorem check_kernel_card (Phi : (∀ i, V i) →ₗ[F2] Rows) :
    Nat.card Phi.ker = 2 ^ ((∑ i, Module.finrank F2 (V i)) - Module.finrank F2 Phi.range) := by
  have hrank := Phi.finrank_range_add_finrank_ker
  rw [Module.finrank_pi_fintype] at hrank
  rw [Module.natCard_eq_pow_finrank (K := F2) (V := Phi.ker)]
  have htwo : Nat.card F2 = 2 := by rw [Nat.card_eq_fintype_card]; exact ZMod.card 2
  rw [htwo]
  congr 1
  omega

variable {J : Type z} (W : J → Type w)
variable [∀ j, AddCommGroup (W j)] [∀ j, Module F2 (W j)]

/-- Stack the actual finite pair checks. The row index can be empty and no
finite-dimensionality of the ambient row space is assumed.
-/
def checkMap (rows : ∀ j, (∀ i, V i) →ₗ[F2] W j) :
    (∀ i, V i) →ₗ[F2] (∀ j, W j) := LinearMap.pi rows

theorem mem_checkMap_ker (rows : ∀ j, (∀ i, V i) →ₗ[F2] W j) (x : ∀ i, V i) :
    x ∈ (checkMap V W rows).ker ↔ ∀ j, rows j x = 0 := by
  change (fun j => rows j x) = 0 ↔ _
  exact funext_iff

theorem checkMap_kernel_card (rows : ∀ j, (∀ i, V i) →ₗ[F2] W j) :
    Nat.card (checkMap V W rows).ker =
      2 ^ ((∑ i, Module.finrank F2 (V i)) - Module.finrank F2 (checkMap V W rows).range) :=
  check_kernel_card V _

end CCO.FiniteKernel.Named
