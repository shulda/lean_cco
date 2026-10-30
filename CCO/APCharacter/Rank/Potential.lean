import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Lean.Elab.Tactic.Omega

/-! The exact base-three potential inequality.  Inactive contributions stay
unchanged; any nonempty active family gives strict decrease. -/
namespace CCO.APCharacter.Rank
open scoped BigOperators
variable {ι : Type*} [Fintype ι]

def potential (k : ι → ℕ) : ℕ := ∑ i, 3 ^ k i

noncomputable def refinedPotential (A : Finset ι) (k left right : ι → ℕ) : ℕ := by
  classical
  exact ∑ i, if i ∈ A then 3 ^ left i + 3 ^ right i else 3 ^ k i

noncomputable def upperPotential (A : Finset ι) (k : ι → ℕ) : ℕ := by
  classical
  exact ∑ i, if i ∈ A then 2 * 3 ^ (k i - 1) else 3 ^ k i

theorem two_children_lt_parent (k : ℕ) (hk : 1 ≤ k) :
    2 * 3 ^ (k - 1) < 3 ^ k := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp only [Nat.succ_sub_one, pow_succ]
  have hp : 0 < 3 ^ n := Nat.pow_pos (by decide)
  omega

theorem refined_le_upper (A : Finset ι) (k left right : ι → ℕ)
    (hl : ∀ i ∈ A, left i ≤ k i - 1) (hr : ∀ i ∈ A, right i ≤ k i - 1) :
    refinedPotential A k left right ≤ upperPotential A k := by
  classical
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i ∈ A
  · simp only [if_pos hi]
    have h1 : 3 ^ left i ≤ (3 : ℕ) ^ (k i - 1) := pow_le_pow_right' (by decide) (hl i hi)
    have h2 : 3 ^ right i ≤ (3 : ℕ) ^ (k i - 1) := pow_le_pow_right' (by decide) (hr i hi)
    omega
  · simp only [if_neg hi, le_refl]

theorem upper_lt_old (A : Finset ι) (k : ι → ℕ) (hA : A.Nonempty)
    (hk : ∀ i ∈ A, 1 ≤ k i) : upperPotential A k < potential k := by
  classical
  obtain ⟨i,hi⟩ := hA
  apply Finset.sum_lt_sum
  · intro j _
    by_cases hj : j ∈ A
    · simp only [if_pos hj]
      exact (two_children_lt_parent (k j) (hk j hj)).le
    · simp only [if_neg hj, le_refl]
  · exact ⟨i,Finset.mem_univ i,by simpa only [if_pos hi] using two_children_lt_parent (k i) (hk i hi)⟩

/-- ACR, including its displayed subtraction form and strict inequality. -/
theorem exact_character_rank_drop (A : Finset ι) (k left right : ι → ℕ)
    (hA : A.Nonempty) (hk : ∀ i ∈ A, 1 ≤ k i)
    (hl : ∀ i ∈ A, left i ≤ k i - 1) (hr : ∀ i ∈ A, right i ≤ k i - 1) :
    refinedPotential A k left right ≤
      potential k - ∑ i ∈ A, 3 ^ k i + ∑ i ∈ A, 2 * 3 ^ (k i - 1) ∧
      potential k - ∑ i ∈ A, 3 ^ k i + ∑ i ∈ A, 2 * 3 ^ (k i - 1) < potential k := by
  classical
  have hle := refined_le_upper A k left right hl hr
  have hlt := upper_lt_old A k hA hk
  have hsum : upperPotential A k + ∑ i ∈ A, 3 ^ k i =
      potential k + ∑ i ∈ A, 2 * 3 ^ (k i - 1) := by
    simp only [upperPotential,potential]
    have ha (f : ι → ℕ) : (∑ i ∈ A, f i) = ∑ i, if i ∈ A then f i else 0 := by
      simp [Finset.sum_ite]
    rw [ha,ha,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> omega
  have hweight : (∑ i ∈ A, 3 ^ k i) ≤ potential k := by
    exact Finset.sum_le_sum_of_subset (Finset.subset_univ A)
  omega

end CCO.APCharacter.Rank
