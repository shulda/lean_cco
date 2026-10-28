import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Explicit elementary estimates for the finite sparse labelled graph argument

These are numerical and finite-sum statements. No graph-existence, probability
concentration or CCO assertion is assumed here.
-/

open scoped BigOperators

noncomputable section

namespace CCO.ParityHasse.Sparse

/-- Cauchy--Schwarz gives the number of same-colour unordered pairs. -/
theorem monochromatic_pair_lower_bound (q : ℕ) (hq : 0 < q)
    (size : Fin q → ℝ) (n : ℝ) (hsum : ∑ d, size d = n)
    (hn : 2 * (q : ℝ) ≤ n) :
    n ^ 2 / (4 * (q : ℝ)) ≤ ((∑ d, size d ^ 2) - n) / 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin q))
    size (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one, hsum] at hcs
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * q)).2
  have hn' : 0 ≤ n := by linarith
  have hextra := mul_nonneg (sub_nonneg.mpr hn) hn'
  nlinarith

/-- The source's lower bound for the Bernoulli mean. -/
theorem mean_lower_bound {N n q r c : ℝ} (hn : 0 < n) (hq : 0 < q)
    (hr : 0 < r) (hc : 0 ≤ c) (hN : n ^ 2 / (4 * q) ≤ N) :
    c * n / (4 * r * q) ≤ N * (c / (n * r)) := by
  have h := mul_le_mul_of_nonneg_right hN
    (div_nonneg hc (mul_nonneg hn.le hr.le))
  have heq : n ^ 2 / (4 * q) * (c / (n * r)) = c * n / (4 * r * q) := by
    field_simp
  exact heq ▸ h

/-- The sole exponential estimate in the elementary lower-tail calculation. -/
theorem exp_neg_one_le_half : Real.exp (-1) ≤ (1 : ℝ) / 2 := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  simpa only [Real.exp_neg, one_div] using
    (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) htwo)

/-- One Bernoulli factor, without a concentration theorem. -/
theorem bernoulli_exp_factor {p : ℝ} (hp : 0 ≤ p) :
    1 - p + p * Real.exp (-1) ≤ Real.exp (-p / 2) := by
  have hmul := mul_le_mul_of_nonneg_left exp_neg_one_le_half hp
  have hlin : 1 - p + p * Real.exp (-1) ≤ 1 - p / 2 := by linarith
  have hexp := Real.add_one_le_exp (-p / 2)
  linarith

/-- Raising the elementary one-factor estimate gives the finite product bound. -/
theorem bernoulli_exp_product {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1) (N : ℕ) :
    (1 - p + p * Real.exp (-1)) ^ N ≤ Real.exp (-(N : ℝ) * p / 2) := by
  have hnonneg : 0 ≤ 1 - p + p * Real.exp (-1) := by positivity
  have h := pow_le_pow_left₀ hnonneg (bernoulli_exp_factor hp) N
  have heq : Real.exp (-p / 2) ^ N = Real.exp (-(N : ℝ) * p / 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  exact heq ▸ h

/-- The source constant, with natural logarithm and positive integer parameters. -/
def sparseConstant (q r : ℕ) : ℝ := 128 * r * q * Real.log ((q : ℝ) + 1)

def sparseDelta (q r : ℕ) : ℝ := sparseConstant q r / (16 * r * q) - Real.log q

theorem sparseConstant_pos {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    0 < sparseConstant q r := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hl : 0 < Real.log ((q : ℝ) + 1) := Real.log_pos (by linarith)
  unfold sparseConstant
  positivity

theorem sparseDelta_pos {q r : ℕ} (hq : 0 < q) (hr : 0 < r) :
    0 < sparseDelta q r := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hl : 0 < Real.log ((q : ℝ) + 1) := Real.log_pos (by linarith)
  have hle : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log hq' (by linarith)
  have heq : sparseDelta q r = 8 * Real.log ((q : ℝ) + 1) - Real.log q := by
    unfold sparseDelta sparseConstant
    field_simp
    <;> ring
  rw [heq]
  linarith

/-- An explicit Archimedean choice, avoiding a limiting-probability argument. -/
theorem exists_sparse_size {q r : ℕ} (hq : 0 < q) (hr : 0 < r)
    {c δ B : ℝ} (hc : 0 < c) (hδ : 0 < δ) :
    ∃ n : ℕ, 2 * q ≤ n ∧ c < n ∧
      (r : ℝ) ^ q * Real.exp (-δ * n) < 1 / 4 ∧
      4 * B < c * n / (16 * r * q) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  let threshold := max ((2 * q : ℕ) : ℝ)
    (max c (max (Real.log (4 * (r : ℝ) ^ q) / δ) (64 * r * q * B / c)))
  obtain ⟨n, hn⟩ := exists_nat_gt threshold
  have h2q : ((2 * q : ℕ) : ℝ) < n := (le_max_left _ _).trans_lt hn
  have hc' : c < n := (le_trans (le_max_left _ _) (le_max_right _ _)).trans_lt hn
  have hlog : Real.log (4 * (r : ℝ) ^ q) / δ < n :=
    (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) (le_max_right _ _)).trans_lt hn
  have hB : 64 * r * q * B / c < n :=
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) (le_max_right _ _)).trans_lt hn
  refine ⟨n, ?_, hc', ?_, ?_⟩
  · exact_mod_cast h2q.le
  · have hln : Real.log (4 * (r : ℝ) ^ q) < δ * n := by
      have hh := (div_lt_iff₀ hδ).mp hlog
      simpa only [mul_comm] using hh
    have hexp : 4 * (r : ℝ) ^ q < Real.exp (δ * n) :=
      (Real.log_lt_iff_lt_exp (by positivity)).mp hln
    rw [show -δ * (n : ℝ) = -(δ * n) by ring, Real.exp_neg]
    have hden : 0 < Real.exp (δ * n) := Real.exp_pos _
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    nlinarith
  · apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * r * q)).2
    have hh := (div_lt_iff₀ hc).mp hB
    nlinarith

/-- All four numerical choices in N02 for the concrete source constant. -/
theorem exists_source_sparse_size {q r : ℕ} (hq : 0 < q) (hr : 0 < r) (B : ℝ) :
    ∃ n : ℕ, 2 * q ≤ n ∧ sparseConstant q r < n ∧
      (r : ℝ) ^ q * Real.exp (-sparseDelta q r * n) < 1 / 4 ∧
      4 * B < sparseConstant q r * n / (16 * r * q) :=
  exists_sparse_size hq hr (sparseConstant_pos hq hr) (sparseDelta_pos hq hr)

end CCO.ParityHasse.Sparse
