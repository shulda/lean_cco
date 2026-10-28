import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Lean.Elab.Tactic.Omega

/-! Finite-cover and binomial bookkeeping. All sets to be counted are first
proved finite. The final power estimate has an explicit natural constant,
so it expresses O(n^r) without an analytic library or limit assumption. -/
universe u v
namespace CCO.RealClosure.Bounds
open scoped BigOperators

/-- A finite union is a genuine surjective image of its finite disjoint sum. -/
theorem finite_family_card_bound {ι : Type u} {M : Type v}
    (I : Finset ι) (f : ι → Set M) (hf : ∀ i, (f i).Finite) :
    (⋃ i ∈ I, f i).Finite ∧ Nat.card (⋃ i ∈ I, f i) ≤ ∑ i ∈ I, Nat.card (f i) := by
  classical
  letI : Fintype ↥I := inferInstance
  letI : ∀ i : ↥I, Fintype (f i.val) := fun i => (hf i.val).fintype
  let domain := Σ i : ↥I, f i.val
  let out : domain → (⋃ i ∈ I, f i) := fun p => ⟨p.2.val,
    Set.mem_iUnion.mpr ⟨p.1.val,Set.mem_iUnion.mpr ⟨p.1.property,p.2.property⟩⟩⟩
  have hout : Function.Surjective out := by
    intro x
    obtain ⟨i,hx⟩ := Set.mem_iUnion.mp x.property
    obtain ⟨hi,hix⟩ := Set.mem_iUnion.mp hx
    exact ⟨⟨⟨i,hi⟩,⟨x.val,hix⟩⟩,rfl⟩
  letI : Finite (⋃ i ∈ I, f i) := Finite.of_surjective out hout
  refine ⟨Set.finite_coe_iff.mp inferInstance,?_⟩
  calc
    _ ≤ Nat.card domain := Nat.card_le_card_of_surjective out hout
    _ = ∑ i : ↥I, Nat.card (f i.val) := Nat.card_sigma
    _ = _ := Finset.sum_coe_sort I (fun i => Nat.card (f i))

noncomputable def smallBases {M : Type u} (A : Finset M) (r : ℕ) : Finset (Finset M) := by
  classical
  exact A.powerset.filter (fun B => 0 < B.card ∧ B.card ≤ r)

@[simp] theorem mem_smallBases {M : Type u} (A : Finset M) (r : ℕ) (B : Finset M) :
    B ∈ smallBases A r ↔ B ⊆ A ∧ 0 < B.card ∧ B.card ≤ r := by
  classical
  simp [smallBases]

/-- Exact sum in the source: j=1 through min(r,n), with no zero-base term. -/
def closurePolynomial (r d n : ℕ) : ℕ :=
  n + ∑ j ∈ Finset.Icc 1 (min r n), n.choose j * d^j

theorem smallBases_weighted_sum {M : Type u} (A : Finset M) (r d : ℕ) :
    ∑ B ∈ smallBases A r, d^B.card =
      ∑ j ∈ Finset.Icc 1 (min r A.card), A.card.choose j * d^j := by
  classical
  have hmaps : ∀ B ∈ smallBases A r, B.card ∈ Finset.Icc 1 (min r A.card) := by
    intro B hB
    obtain ⟨hBA,hpos,hBr⟩ := (mem_smallBases A r B).mp hB
    exact Finset.mem_Icc.mpr ⟨hpos,le_min hBr (Finset.card_le_card hBA)⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun B : Finset M => d^B.card)]
  apply Finset.sum_congr rfl
  intro j hj
  obtain ⟨hjpos,hjbound⟩ := Finset.mem_Icc.mp hj
  have hjr := (le_min_iff.mp hjbound).1
  have hfilter : (smallBases A r).filter (fun B => B.card = j) = A.powersetCard j := by
    ext B
    simp only [Finset.mem_filter,mem_smallBases,Finset.mem_powersetCard]
    constructor
    · rintro ⟨⟨hBA,_,_⟩,hcard⟩
      exact ⟨hBA,hcard⟩
    · rintro ⟨hBA,hcard⟩
      exact ⟨⟨hBA,by omega,by omega⟩,hcard⟩
  rw [hfilter]
  calc
    ∑ B ∈ A.powersetCard j, d^B.card = ∑ _B ∈ A.powersetCard j, d^j := by
      apply Finset.sum_congr rfl
      intro B hB
      rw [(Finset.mem_powersetCard.mp hB).2]
    _ = _ := by simp only [Finset.sum_const,Finset.card_powersetCard,nsmul_eq_mul,Nat.cast_id]

@[simp] theorem closurePolynomial_zero (r d : ℕ) : closurePolynomial r d 0 = 0 := by
  simp [closurePolynomial]

/-- An explicit model-dependent coefficient for the sharp exponent r. -/
def growthCoefficient (r d : ℕ) : ℕ := 1 + r * (max 1 d)^r

theorem closurePolynomial_power_bound (r d n : ℕ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    closurePolynomial r d n ≤ growthCoefficient r d * n^r := by
  have hn0 : 0 < n := by omega
  have hD : 0 < max 1 d := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
  have hnPow : n ≤ n^r := by
    have hh := Nat.pow_le_pow_right hn0 hr
    simpa only [pow_one] using hh
  have hsum : (∑ j ∈ Finset.Icc 1 (min r n), n.choose j * d^j) ≤
      (min r n) * (n^r * (max 1 d)^r) := by
    calc
      _ ≤ ∑ _j ∈ Finset.Icc 1 (min r n), n^r * (max 1 d)^r := by
        apply Finset.sum_le_sum
        intro j hj
        have hjr : j ≤ r := (le_min_iff.mp (Finset.mem_Icc.mp hj).2).1
        have hc : n.choose j ≤ n^r :=
          (Nat.choose_le_pow n j).trans (Nat.pow_le_pow_right hn0 hjr)
        have hd : d^j ≤ (max 1 d)^r :=
          (Nat.pow_le_pow_left (le_max_right 1 d) j).trans (Nat.pow_le_pow_right hD hjr)
        exact Nat.mul_le_mul hc hd
      _ = _ := by simp only [Finset.sum_const,Nat.card_Icc,nsmul_eq_mul,Nat.add_sub_cancel,Nat.cast_id]
  have hsum' : (∑ j ∈ Finset.Icc 1 (min r n), n.choose j * d^j) ≤
      r * (n^r * (max 1 d)^r) :=
    hsum.trans (Nat.mul_le_mul_right _ (min_le_left _ _))
  calc
    closurePolynomial r d n ≤ n^r + r * (n^r * (max 1 d)^r) :=
      Nat.add_le_add hnPow hsum'
    _ = growthCoefficient r d * n^r := by
      simp only [growthCoefficient,Nat.add_mul,Nat.one_mul]
      simp only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm]

/-- Explicit O(n^r): the one natural coefficient works for every n>=1. -/
theorem closurePolynomial_eventual_power (r d : ℕ) (hr : 1 ≤ r) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n → closurePolynomial r d n ≤ C*n^r :=
  ⟨growthCoefficient r d,fun n hn => closurePolynomial_power_bound r d n hr hn⟩
end CCO.RealClosure.Bounds
