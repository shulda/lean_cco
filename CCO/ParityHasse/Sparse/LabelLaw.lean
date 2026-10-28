import CCO.ParityHasse.Sparse.Bernoulli
import Mathlib.Data.Fintype.Option

/-! The actual finite product law for labels: `none` has weight `1-ρ`,
and each of the `r` positive labels has weight `ρ/r`. -/
open scoped BigOperators
namespace CCO.ParityHasse.Sparse

universe u

noncomputable def labelWeight (r : ℕ) (ρ : ℝ) : Option (Fin r) → ℝ
  | none => 1 - ρ
  | some _ => ρ / r

theorem labelWeight_nonneg {r : ℕ} {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    ∀ a, 0 ≤ labelWeight r ρ a := by
  rintro (_ | a)
  · exact sub_nonneg.mpr hρ1
  · exact div_nonneg hρ (Nat.cast_nonneg _)

theorem labelWeight_sum {r : ℕ} (hr : 0 < r) (ρ : ℝ) :
    ∑ a, labelWeight r ρ a = 1 := by
  have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [Fintype.sum_option]
  simp only [labelWeight, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  <;> ring

variable {I : Type u} [Fintype I] [DecidableEq I]

noncomputable def labelLaw {r : ℕ} (hr : 0 < r) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) : FiniteLaw (I → Option (Fin r)) :=
  productLaw (fun _ => labelWeight r ρ) (fun _ => labelWeight_nonneg hρ hρ1)
    (fun _ => labelWeight_sum hr ρ)

noncomputable def requestedHits {r : ℕ} (K : Finset I) (target : I → Fin r)
    (ω : I → Option (Fin r)) : ℝ :=
  successCount (fun i a => i ∈ K ∧ a = some (target i)) ω

theorem requestedHits_eq_card {r : ℕ} (K : Finset I) (target : I → Fin r)
    (ω : I → Option (Fin r)) : requestedHits K target ω =
      ((Finset.univ.filter (fun i => i ∈ K ∧ ω i = some (target i))).card : ℝ) := by
  classical
  unfold requestedHits successCount
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> norm_num

theorem requested_success_probability {r : ℕ} (ρ : ℝ) (K : Finset I)
    (target : I → Fin r) (i : I) :
    successProbability (fun _ : I => labelWeight r ρ)
      (fun i a => i ∈ K ∧ a = some (target i)) i = if i ∈ K then ρ / r else 0 := by
  classical
  by_cases hi : i ∈ K
  · simp [successProbability, hi, labelWeight, Finset.sum_ite_eq']
  · simp [successProbability, hi]

theorem requested_mean {r : ℕ} (ρ : ℝ) (K : Finset I) (target : I → Fin r) :
    meanCount (fun _ : I => labelWeight r ρ)
      (fun i a => i ∈ K ∧ a = some (target i)) = (K.card : ℝ) * (ρ / r) := by
  classical
  unfold meanCount
  simp_rw [requested_success_probability]
  simp

theorem requested_lower_tail {r : ℕ} (hr : 0 < r) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (K : Finset I) (target : I → Fin r) :
    (labelLaw (I := I) hr hρ hρ1).prob
      (fun ω => requestedHits K target ω < (K.card : ℝ) * (ρ / r) / 4) ≤
        Real.exp (-((K.card : ℝ) * (ρ / r)) / 4) := by
  classical
  have h := bernoulli_lower_tail (fun _ : I => labelWeight r ρ)
    (fun _ => labelWeight_nonneg hρ hρ1) (fun _ => labelWeight_sum hr ρ)
    (fun i a => i ∈ K ∧ a = some (target i))
  rw [requested_mean] at h
  exact h

/-- Independent coordinates carry some positive label with probability ρ. -/
theorem positive_labels_probability {r : ℕ} (hr : 0 < r) {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (K : Finset I) :
    (labelLaw (I := I) hr hρ hρ1).prob
      (fun ω => ∀ i ∈ K, ω i ≠ none) = ρ ^ K.card := by
  classical
  have h := product_prob_all (fun _ : I => labelWeight r ρ)
    (fun _ => labelWeight_nonneg hρ hρ1) (fun _ => labelWeight_sum hr ρ)
    (fun i a => i ∈ K → a ≠ none)
  have heq (i : I) :
      (∑ a, if i ∈ K → a ≠ none then labelWeight r ρ a else 0) =
        if i ∈ K then ρ else 1 := by
    by_cases hi : i ∈ K
    · rw [if_pos hi, Fintype.sum_option]
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
      simp only [hi, true_implies, ne_eq, not_true_eq_false, if_false, labelWeight,
        reduceCtorEq, not_false_eq_true, if_true, zero_add,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · simp only [hi, false_implies, if_true, if_false]
      exact labelWeight_sum hr ρ
  simp_rw [heq] at h
  simpa only [labelLaw, Finset.prod_ite_mem, Finset.prod_const_one, mul_one,
    Finset.prod_const, Finset.univ_inter] using h

end CCO.ParityHasse.Sparse
