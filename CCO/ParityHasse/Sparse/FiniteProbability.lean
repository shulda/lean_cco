import CCO.ParityHasse.Sparse.Bounds
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

/-! Elementary finite probability. All probabilities are explicit finite weighted sums;
no concentration theorem or infinite probability space is used. -/

open scoped BigOperators
namespace CCO.ParityHasse.Sparse

universe u v

structure FiniteLaw (Ω : Type u) [Fintype Ω] where
  mass : Ω → ℝ
  nonneg : ∀ ω, 0 ≤ mass ω
  total : ∑ ω, mass ω = 1

namespace FiniteLaw
variable {Ω : Type u} [Fintype Ω]

noncomputable def prob (L : FiniteLaw Ω) (P : Ω → Prop) : ℝ := by
  classical
  exact ∑ ω, if P ω then L.mass ω else 0

noncomputable def expect (L : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  ∑ ω, L.mass ω * f ω

theorem prob_nonneg (L : FiniteLaw Ω) (P : Ω → Prop) : 0 ≤ L.prob P := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split_ifs <;> simp_all [L.nonneg]

theorem prob_le_one (L : FiniteLaw Ω) (P : Ω → Prop) : L.prob P ≤ 1 := by
  classical
  rw [← L.total]
  apply Finset.sum_le_sum
  intro ω _
  split_ifs <;> simp_all [L.nonneg]

theorem exists_not_of_prob_lt_one (L : FiniteLaw Ω) {P : Ω → Prop}
    (h : L.prob P < 1) : ∃ ω, ¬ P ω := by
  classical
  by_contra hn
  push_neg at hn
  have : L.prob P = 1 := by simp [prob, hn, L.total]
  linarith

theorem prob_congr (L : FiniteLaw Ω) {P Q : Ω → Prop}
    (h : ∀ ω, P ω ↔ Q ω) : L.prob P = L.prob Q := by
  classical
  unfold prob
  apply Finset.sum_congr rfl
  intro ω _
  simp only [h ω]

theorem expect_indicator (L : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P] :
    L.expect (fun ω => if P ω then (1 : ℝ) else 0) = L.prob P := by
  classical
  unfold expect prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : P ω <;> simp [h]

theorem prob_mono (L : FiniteLaw Ω) {P Q : Ω → Prop}
    (h : ∀ ω, P ω → Q ω) : L.prob P ≤ L.prob Q := by
  classical
  apply Finset.sum_le_sum
  intro ω _
  split_ifs with hp hq hq <;> simp_all [L.nonneg]

theorem prob_or_le (L : FiniteLaw Ω) (P Q : Ω → Prop) :
    L.prob (fun ω => P ω ∨ Q ω) ≤ L.prob P + L.prob Q := by
  classical
  unfold prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro ω _
  split_ifs <;> simp_all [L.nonneg]

theorem prob_exists_le {I : Type v} [Fintype I] (L : FiniteLaw Ω)
    (P : I → Ω → Prop) :
    L.prob (fun ω => ∃ i, P i ω) ≤ ∑ i, L.prob (P i) := by
  classical
  unfold prob
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : ∃ i, P i ω
  · simp only [if_pos h]
    obtain ⟨i, hi⟩ := h
    exact (by simpa [hi] using
      (Finset.single_le_sum (f := fun i => if P i ω then L.mass ω else 0)
        (fun i _ => by split_ifs <;> simp_all [L.nonneg]) (Finset.mem_univ i)))
  · simp only [if_neg h]
    exact Finset.sum_nonneg fun i _ => by split_ifs <;> simp_all [L.nonneg]

theorem expect_nonneg (L : FiniteLaw Ω) (f : Ω → ℝ)
    (h : ∀ ω, 0 ≤ f ω) : 0 ≤ L.expect f :=
  Finset.sum_nonneg fun ω _ => mul_nonneg (L.nonneg ω) (h ω)

theorem markov (L : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω)
    {a : ℝ} (ha : 0 < a) :
    L.prob (fun ω => a ≤ f ω) ≤ L.expect f / a := by
  classical
  apply (le_div_iff₀ ha).2
  unfold prob expect
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro ω _
  by_cases h : a ≤ f ω
  · simp only [if_pos h]
    exact mul_le_mul_of_nonneg_left h (L.nonneg ω)
  · simp only [if_neg h, zero_mul]
    exact mul_nonneg (L.nonneg ω) (hf ω)

theorem expect_sum {I : Type v} [Fintype I] (L : FiniteLaw Ω)
    (f : I → Ω → ℝ) :
    L.expect (fun ω => ∑ i, f i ω) = ∑ i, L.expect (f i) := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- The source lower-tail estimate: exponential Markov, not Chernoff. -/
theorem exponential_lower_tail (L : FiniteLaw Ω) (X : Ω → ℝ) (μ : ℝ)
    (hm : L.expect (fun ω => Real.exp (-X ω)) ≤ Real.exp (-μ / 2)) :
    L.prob (fun ω => X ω < μ / 4) ≤ Real.exp (-μ / 4) := by
  have hp := L.prob_mono (P := fun ω => X ω < μ / 4)
    (Q := fun ω => Real.exp (-μ / 4) ≤ Real.exp (-X ω)) (by
      intro ω h
      apply Real.exp_le_exp.mpr
      linarith)
  have hk := L.markov (fun ω => Real.exp (-X ω))
    (fun ω => (Real.exp_pos _).le) (Real.exp_pos (-μ / 4))
  refine hp.trans (hk.trans ?_)
  apply (div_le_iff₀ (Real.exp_pos (-μ / 4))).2
  calc
    L.expect (fun ω => Real.exp (-X ω)) ≤ Real.exp (-μ / 2) := hm
    _ = Real.exp (-μ / 4) * Real.exp (-μ / 4) := by
      rw [← Real.exp_add]
      congr 1
      ring

end FiniteLaw

section Product
variable {I : Type u} {A : Type v} [Fintype I] [DecidableEq I] [Fintype A]

noncomputable def productLaw (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hs : ∀ i, ∑ a, p i a = 1) : FiniteLaw (I → A) where
  mass ω := ∏ i, p i (ω i)
  nonneg ω := Finset.prod_nonneg fun i _ => hp i (ω i)
  total := by rw [← Fintype.prod_sum]; simp [hs]

theorem product_expect (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hs : ∀ i, ∑ a, p i a = 1) (f : I → A → ℝ) :
    (productLaw p hp hs).expect (fun ω => ∏ i, f i (ω i)) =
      ∏ i, ∑ a, p i a * f i a := by
  classical
  unfold FiniteLaw.expect productLaw
  simp only
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro ω _
  exact (Finset.prod_mul_distrib).symm

theorem product_prob_all (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (hs : ∀ i, ∑ a, p i a = 1) (P : I → A → Prop) [∀ i, DecidablePred (P i)] :
    (productLaw p hp hs).prob (fun ω => ∀ i, P i (ω i)) =
      ∏ i, ∑ a, if P i a then p i a else 0 := by
  classical
  have hbool (ω : I → A) :
      (∏ i, if P i (ω i) then (1 : ℝ) else 0) =
        if ∀ i, P i (ω i) then 1 else 0 := by
    by_cases h : ∀ i, P i (ω i)
    · simp [h]
    · obtain ⟨i, hi⟩ : ∃ i, ¬ P i (ω i) := not_forall.mp h
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  have he := product_expect p hp hs (fun i a => if P i a then (1 : ℝ) else 0)
  simp only [hbool, FiniteLaw.expect, FiniteLaw.prob, mul_ite, mul_one, mul_zero] at he
  rw [← he]
  unfold FiniteLaw.prob
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : ∀ i, P i (ω i) <;> simp [h]

end Product
end CCO.ParityHasse.Sparse
