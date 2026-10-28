import CCO.ParityHasse.Sparse.GraphLaw
import CCO.ParityHasse.Sparse.Deletion

/-! Finite union and Markov bounds produce an actual robust labelled outcome.
The cycle expectation premise here is the intermediate numerical estimate,
proved for the actual graph law by the separate cycle-expectation module. -/

open scoped BigOperators
namespace CCO.ParityHasse.Sparse
noncomputable section

lemma union_failure_factor (q r n : ℕ) (hq : 0 < q) (c : ℝ) :
    (q : ℝ) ^ n * (r : ℝ) ^ q * Real.exp (-c * n / (16 * r * q)) =
      (r : ℝ) ^ q * Real.exp (-(c / (16 * r * q) - Real.log q) * n) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have heq : (q : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hq']
  rw [heq]
  calc
    _ = (r : ℝ) ^ q * (Real.exp ((n : ℝ) * Real.log q) *
        Real.exp (-c * n / (16 * r * q))) := by ring
    _ = (r : ℝ) ^ q * Real.exp ((n : ℝ) * Real.log q + -c * n / (16 * r * q)) := by
      rw [Real.exp_add]
    _ = _ := by congr 2; ring

/-- Positive probability of simultaneous robust requests and a small cycle count. -/
theorem exists_good_outcome {q r n g : ℕ} (hq : 0 < q) (hr : 0 < r)
    (hn : 0 < n) (hsize : 2 * q ≤ n) {c B : ℝ} (hc : 0 < c)
    (hcn : c < (n : ℝ)) (hB : 0 < B)
    (hUnion : (r : ℝ) ^ q *
      Real.exp (-(c / (16 * r * q) - Real.log q) * n) < 1 / 4)
    (hGap : 4 * B < c * n / (16 * r * q))
    (hExpect : (labelLaw (I := Sym2 (Fin n)) hr
      (div_nonneg hc.le (Nat.cast_nonneg n))
      ((div_le_one (by exact_mod_cast hn)).2 hcn.le)).expect
        (fun ω => cycleMass g (presentEdges ω)) ≤ B) :
    ∃ ω : EdgeLabelling (Fin n) r,
      (∀ (κ : Fin n → Fin q) (h : Fin q → Fin r),
        4 * B < requestedHits (monochromaticPairs κ) (requestedTarget κ h) ω) ∧
      cycleMass g (presentEdges ω) ≤ 4 * B := by
  classical
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hρ : 0 ≤ c / n := div_nonneg hc.le hn'.le
  have hρ1 : c / n ≤ 1 := (div_le_one hn').2 hcn.le
  let L := labelLaw (I := Sym2 (Fin n)) hr hρ hρ1
  let μ (κ : Fin n → Fin q) : ℝ :=
    ((monochromaticPairs κ).card : ℝ) * ((c / n) / r)
  have hmean (κ : Fin n → Fin q) : c * n / (16 * r * q) ≤ μ κ / 4 := by
    have hN : (n : ℝ) ^ 2 / (4 * q) ≤ ((monochromaticPairs κ).card : ℝ) := by
      simpa only [Fintype.card_fin] using actual_monochromatic_pair_lower_bound κ hq (by simpa only [Fintype.card_fin] using hsize)
    have hm : c * n / (4 * r * q) ≤ μ κ := by
      simpa only [μ, div_div] using mean_lower_bound hn' hq' hr' hc.le hN
    have hm' := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * r * q)).mp hm
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * r * q)).2
    nlinarith
  have htail (κ : Fin n → Fin q) (h : Fin q → Fin r) :
      L.prob (fun ω => requestedHits (monochromaticPairs κ) (requestedTarget κ h) ω < μ κ / 4) ≤
        Real.exp (-c * n / (16 * r * q)) := by
    have ht := requested_lower_tail (I := Sym2 (Fin n)) hr hρ hρ1
      (monochromaticPairs κ) (requestedTarget κ h)
    have he : Real.exp (-μ κ / 4) ≤ Real.exp (-c * n / (16 * r * q)) := by
      apply Real.exp_le_exp.mpr
      simpa only [neg_div, neg_mul] using (neg_le_neg (hmean κ))
    exact ht.trans he
  let Bad (ω : EdgeLabelling (Fin n) r) : Prop :=
    ∃ τ : (Fin n → Fin q) × (Fin q → Fin r),
      requestedHits (monochromaticPairs τ.1) (requestedTarget τ.1 τ.2) ω < μ τ.1 / 4
  have hBad : L.prob Bad < 1 / 4 := by
    have hb := L.prob_exists_le (fun τ : (Fin n → Fin q) × (Fin q → Fin r) =>
      fun ω => requestedHits (monochromaticPairs τ.1) (requestedTarget τ.1 τ.2) ω < μ τ.1 / 4)
    have hs : (∑ τ : (Fin n → Fin q) × (Fin q → Fin r),
        L.prob (fun ω => requestedHits (monochromaticPairs τ.1) (requestedTarget τ.1 τ.2) ω < μ τ.1 / 4)) ≤
        (q : ℝ) ^ n * (r : ℝ) ^ q * Real.exp (-c * n / (16 * r * q)) := by
      calc
        _ ≤ ∑ _τ : (Fin n → Fin q) × (Fin q → Fin r),
            Real.exp (-c * n / (16 * r * q)) :=
          Finset.sum_le_sum (fun τ _ => htail τ.1 τ.2)
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod,
            Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, Nat.cast_pow]
    have hfac := union_failure_factor q r n hq c
    exact (hb.trans hs).trans_lt (hfac ▸ hUnion)
  have hCycles : L.prob (fun ω => 4 * B < cycleMass g (presentEdges ω)) ≤ 1 / 4 := by
    have hm := L.markov (fun ω => cycleMass g (presentEdges ω))
      (fun ω => cycleMass_nonneg g _) (by positivity : 0 < 4 * B)
    have hsub := L.prob_mono (P := fun ω => 4 * B < cycleMass g (presentEdges ω))
      (Q := fun ω => 4 * B ≤ cycleMass g (presentEdges ω)) (fun ω h => h.le)
    have he : L.expect (fun ω => cycleMass g (presentEdges ω)) / (4 * B) ≤ B / (4 * B) :=
      div_le_div_of_nonneg_right hExpect (by positivity)
    have heq : B / (4 * B) = (1 : ℝ) / 4 := by field_simp
    exact hsub.trans (hm.trans (he.trans_eq heq))
  have hTotal : L.prob (fun ω => Bad ω ∨ 4 * B < cycleMass g (presentEdges ω)) < 1 := by
    have h := L.prob_or_le Bad (fun ω => 4 * B < cycleMass g (presentEdges ω))
    linarith
  obtain ⟨ω, hω⟩ := L.exists_not_of_prob_lt_one hTotal
  have hnot := not_or.mp hω
  refine ⟨ω, ?_, le_of_not_gt hnot.2⟩
  intro κ h
  have hlow : μ κ / 4 ≤ requestedHits (monochromaticPairs κ) (requestedTarget κ h) ω := by
    apply le_of_not_gt
    intro hbad
    exact hnot.1 ⟨(κ, h), hbad⟩
  exact hGap.trans_le ((hmean κ).trans hlow)

end
end CCO.ParityHasse.Sparse
