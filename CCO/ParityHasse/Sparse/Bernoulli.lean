import CCO.ParityHasse.Sparse.FiniteProbability
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! Elementary Laplace-transform and lower-tail estimates for finite independent
Bernoulli indicators. Independence is evaluated by a finite product of sums. -/
open scoped BigOperators
namespace CCO.ParityHasse.Sparse

universe u v
variable {I : Type u} {A : Type v} [Fintype I] [DecidableEq I] [Fintype A]

noncomputable def successProbability (p : I → A → ℝ) (P : I → A → Prop) (i : I) : ℝ := by
  classical
  exact ∑ a, if P i a then p i a else 0

noncomputable def successCount (P : I → A → Prop) (ω : I → A) : ℝ := by
  classical
  exact ∑ i, if P i (ω i) then 1 else 0

noncomputable def meanCount (p : I → A → ℝ) (P : I → A → Prop) : ℝ :=
  ∑ i, successProbability p P i

theorem successProbability_nonneg (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (P : I → A → Prop) (i : I) : 0 ≤ successProbability p P i := by
  classical
  exact Finset.sum_nonneg fun a _ => by split_ifs <;> simp_all [hp]

theorem successProbability_le_one (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hs : ∀ i, ∑ a, p i a = 1) (P : I → A → Prop) (i : I) :
    successProbability p P i ≤ 1 :=
  (FiniteLaw.mk (p i) (hp i) (hs i)).prob_le_one (P i)

theorem coordinate_exp (p : I → A → ℝ) (hs : ∀ i, ∑ a, p i a = 1)
    (P : I → A → Prop) [∀ i, DecidablePred (P i)] (i : I) :
    (∑ a, p i a * Real.exp (-(if P i a then (1 : ℝ) else 0))) =
      1 - successProbability p P i + successProbability p P i * Real.exp (-1) := by
  classical
  have h (a : A) : p i a * Real.exp (-(if P i a then (1 : ℝ) else 0)) =
      p i a + (Real.exp (-1) - 1) * (if P i a then p i a else 0) := by
    by_cases ha : P i a <;> simp [ha] <;> ring
  simp_rw [h]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, hs i]
  have heq : (∑ a, if P i a then p i a else 0) = successProbability p P i := by
    unfold successProbability
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : P i a <;> simp [h]
  rw [heq]
  ring

theorem bernoulli_laplace (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hs : ∀ i, ∑ a, p i a = 1) (P : I → A → Prop) :
    (productLaw p hp hs).expect (fun ω => Real.exp (-successCount P ω)) ≤
      Real.exp (-meanCount p P / 2) := by
  classical
  have hexp (ω : I → A) : Real.exp (-successCount P ω) =
      ∏ i, Real.exp (-(if P i (ω i) then (1 : ℝ) else 0)) := by
    unfold successCount
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
  simp_rw [hexp]
  rw [product_expect p hp hs (fun i a => Real.exp (-(if P i a then (1 : ℝ) else 0)))]
  simp_rw [coordinate_exp p hs P]
  calc
    _ ≤ ∏ i, Real.exp (-successProbability p P i / 2) := by
      apply Finset.prod_le_prod₀
      · intro i _
        have hp₀ := successProbability_nonneg p hp P i
        have hp₁ := successProbability_le_one p hp hs P i
        positivity
      · intro i _
        exact bernoulli_exp_factor (successProbability_nonneg p hp P i)
    _ = Real.exp (-meanCount p P / 2) := by
      rw [← Real.exp_sum]
      congr 1
      unfold meanCount
      rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem bernoulli_lower_tail (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hs : ∀ i, ∑ a, p i a = 1) (P : I → A → Prop) :
    (productLaw p hp hs).prob (fun ω => successCount P ω < meanCount p P / 4) ≤
      Real.exp (-meanCount p P / 4) :=
  FiniteLaw.exponential_lower_tail _ _ _ (bernoulli_laplace p hp hs P)

end CCO.ParityHasse.Sparse
