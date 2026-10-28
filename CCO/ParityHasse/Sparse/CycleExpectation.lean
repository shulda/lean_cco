import CCO.ParityHasse.Sparse.GraphLaw
import CCO.ParityHasse.Sparse.Deletion
import Mathlib.Algebra.BigOperators.Field

/-! The exact expected short-cycle bound c^ℓ/(2ℓ), using normalized oriented
cycle codes rather than postulating a graph-existence theorem. -/
open scoped BigOperators
namespace CCO.ParityHasse.Sparse
noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]

lemma cycleCode_card_le {ℓ : ℕ} [NeZero ℓ] :
    Fintype.card (CycleCode V ℓ) ≤ Fintype.card V ^ ℓ := by
  have h := Fintype.card_le_of_injective (fun f : CycleCode V ℓ => (f : ZMod ℓ → V))
    (fun f g h => Function.Embedding.ext (congrFun h))
  simpa only [Fintype.card_fun, ZMod.card] using h

lemma supportedCodes_card_as_sum {ℓ : ℕ} [NeZero ℓ] (E : Finset (Sym2 V)) :
    ((supportedCodes (ℓ := ℓ) E).card : ℝ) =
      ∑ f : CycleCode V ℓ, if cyclicEdges f ⊆ E then (1 : ℝ) else 0 := by
  classical
  unfold supportedCodes
  rw [Finset.card_eq_sum_ones]
  simp only [Nat.cast_sum, Nat.cast_one, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro f _
  split_ifs <;> norm_num

lemma expect_supportedCodes {r ℓ : ℕ} (hr : 0 < r) [NeZero ℓ]
    (hℓ : 3 ≤ ℓ) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (labelLaw (I := Sym2 V) hr hρ hρ1).expect
      (fun ω => ((supportedCodes (ℓ := ℓ) (presentEdges ω)).card : ℝ)) =
        (Fintype.card (CycleCode V ℓ) : ℝ) * ρ ^ ℓ := by
  classical
  simp_rw [supportedCodes_card_as_sum]
  rw [FiniteLaw.expect_sum]
  have he (f : CycleCode V ℓ) :
      (labelLaw (I := Sym2 V) hr hρ hρ1).expect
        (fun ω => if cyclicEdges f ⊆ presentEdges ω then (1 : ℝ) else 0) = ρ ^ ℓ := by
    rw [FiniteLaw.expect_indicator, cycle_probability hr hℓ hρ hρ1]
  simp_rw [he]
  simp

lemma expect_div {Ω : Type*} [Fintype Ω] (L : FiniteLaw Ω) (f : Ω → ℝ) (a : ℝ) :
    L.expect (fun ω => f ω / a) = L.expect f / a := by
  unfold FiniteLaw.expect
  simp only [mul_div_assoc, Finset.sum_div]

def cycleBudget (c : ℝ) (g : ℕ) : ℝ :=
  ∑ ℓ : ShortLength g, c ^ ℓ.1.val / (2 * ℓ.1.val)

lemma cycleBudget_pos {c : ℝ} (hc : 0 < c) {g : ℕ} (hg : 3 ≤ g) :
    0 < cycleBudget c g := by
  let ℓ₃ : ShortLength g := ⟨⟨3, by omega⟩, by change 3 ≤ 3; omega⟩
  have hp : 0 < c ^ ℓ₃.1.val / (2 * ℓ₃.1.val : ℝ) := by
    change 0 < c ^ 3 / (2 * (3 : ℝ))
    positivity
  apply hp.trans_le
  unfold cycleBudget
  exact Finset.single_le_sum (f := fun ℓ : ShortLength g =>
    c ^ ℓ.1.val / (2 * ℓ.1.val)) (fun ℓ _ => by positivity) (Finset.mem_univ ℓ₃)

/-- N02's precise B bound. Lengths beyond the vertex set have zero codes. -/
theorem expect_cycleMass_le {n r g : ℕ} (hn : 0 < n) (hr : 0 < r)
    {c : ℝ} (hc : 0 ≤ c) (hcn : c ≤ n) :
    (labelLaw (I := Sym2 (Fin n)) hr (div_nonneg hc (Nat.cast_nonneg n))
      ((div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).2 hcn)).expect
      (fun ω => cycleMass g (presentEdges ω)) ≤ cycleBudget c g := by
  classical
  let hρ := div_nonneg hc (Nat.cast_nonneg n)
  let hρ1 := (div_le_one (by exact_mod_cast hn : (0 : ℝ) < n)).2 hcn
  unfold cycleMass cycleBudget
  rw [FiniteLaw.expect_sum]
  apply Finset.sum_le_sum
  intro ℓ _
  unfold cycleTerm
  rw [expect_div, expect_supportedCodes hr ℓ.2 hρ hρ1]
  have hcard : (Fintype.card (CycleCode (Fin n) ℓ.1.val) : ℝ) ≤ (n : ℝ) ^ ℓ.1.val := by
    have hnat : Fintype.card (CycleCode (Fin n) ℓ.1.val) ≤ n ^ ℓ.1.val := by
      simpa only [Fintype.card_fin] using (cycleCode_card_le (V := Fin n) (ℓ := ℓ.1.val))
    exact_mod_cast hnat
  have hmul := mul_le_mul_of_nonneg_right hcard (pow_nonneg hρ ℓ.1.val)
  have hcan : (n : ℝ) ^ ℓ.1.val * (c / n) ^ ℓ.1.val = c ^ ℓ.1.val := by
    rw [← mul_pow]
    congr 1
    exact mul_div_cancel₀ c (by exact_mod_cast hn.ne')
  rw [hcan] at hmul
  exact div_le_div_of_nonneg_right hmul (by positivity)

end
end CCO.ParityHasse.Sparse
