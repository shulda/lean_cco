import CCO.FiniteFibres.Group.Counting
import Mathlib.Data.ZMod.QuotientGroup

assert_not_exists exists_prime_orderOf_dvd_card IsPGroup Sylow

/-! C09–C11: a local Cauchy proof by cyclic rotation of product-one tuples.
The tuple equivalence and elementary rotations are expanded here. No Cauchy
theorem, Sylow theorem or p-group theorem is used. -/

namespace CCO.FiniteFibres.Group
open Equiv Equiv.Perm Fintype MulAction

variable (K : Type*) [Group K]

def ProductOne (n : ℕ) := {v : List.Vector K n // v.toList.prod = 1}

namespace ProductOne

/-- The first n entries determine the LAST entry uniquely, also for a
noncommutative group. This is the source's literal completion request. -/
theorem last_entry_iff (l : List K) (g : K) :
    (l ++ [g]).prod = 1 ↔ g = l.prod⁻¹ := by
  rw [List.prod_append,List.prod_singleton]
  exact ⟨eq_inv_of_mul_eq_one_right,fun h => by rw [h,mul_inv_cancel]⟩

/-- A one-step cyclic rotation conjugates the product rather than assuming
that different entries commute. -/
theorem rotated_product (g : K) (l : List K) :
    (l ++ [g]).prod = g⁻¹ * (g :: l).prod * g := by
  simp only [List.prod_append,List.prod_singleton,List.prod_cons,List.prod_nil,mul_one,
    inv_mul_cancel_left]

def complete (n : ℕ) : List.Vector K n ≃ ProductOne K (n+1) where
  toFun v := ⟨v.toList.prod⁻¹ ::ᵥ v,by
    change (v.toList.prod⁻¹ :: v.toList).prod = 1
    simp only [List.prod_cons,inv_mul_cancel]⟩
  invFun v := v.val.tail
  left_inv v := v.tail_cons v.toList.prod⁻¹
  right_inv v := Subtype.ext (by
    calc
      v.val.tail.toList.prod⁻¹ ::ᵥ v.val.tail = v.val.head ::ᵥ v.val.tail :=
        congrArg (· ::ᵥ v.val.tail) (Eq.symm (eq_inv_of_mul_eq_one_left (by
          rw [← List.prod_cons,← List.Vector.toList_cons,v.val.cons_head_tail]
          exact v.property)))
      _ = v.val := v.val.cons_head_tail)

instance uniqueZero : Unique (ProductOne K 0) where
  default := ⟨List.Vector.nil,rfl⟩
  uniq v := Subtype.ext v.val.eq_nil

def delete : ∀ n, ProductOne K n ≃ List.Vector K (n-1)
  | 0 => {
      toFun := fun _ => List.Vector.nil
      invFun := fun _ => default
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun v => v.eq_nil.symm }
  | n+1 => (complete K n).symm

instance finite (n : ℕ) [Finite K] : Finite (ProductOne K n) :=
  Finite.of_equiv (List.Vector K (n-1)) (delete K n).symm

/-- Exactly the first p−1 free coordinates determine the product-one tuple. -/
theorem count (n : ℕ) [Finite K] : Nat.card (ProductOne K n) = Nat.card K ^ (n-1) := by
  letI := Fintype.ofFinite K
  rw [Nat.card_congr (delete K n)]
  simp only [Nat.card_eq_fintype_card,card_vector]

def rotate {n : ℕ} (v : ProductOne K n) (k : ℕ) : ProductOne K n :=
  ⟨⟨v.val.toList.rotate k,(v.val.toList.length_rotate k).trans v.val.property⟩,
    List.prod_rotate_eq_one_of_prod_eq_one v.property k⟩

theorem rotate_zero {n : ℕ} (v : ProductOne K n) : rotate K v 0 = v :=
  Subtype.ext (Subtype.ext v.val.toList.rotate_zero)

theorem rotate_rotate {n : ℕ} (v : ProductOne K n) (j k : ℕ) :
    rotate K (rotate K v j) k = rotate K v (j+k) :=
  Subtype.ext (Subtype.ext (v.val.toList.rotate_rotate j k))

theorem rotate_length {n : ℕ} (v : ProductOne K n) : rotate K v n = v :=
  Subtype.ext (Subtype.ext ((congrArg _ v.val.property.symm).trans v.val.toList.rotate_length))

theorem rotation_fixed_iff_constant {n : ℕ} (v : ProductOne K n) :
    rotate K v 1 = v ↔ ∃ g : K, v.val.toList = List.replicate n g := by
  constructor
  · intro hv
    obtain ⟨g,hg⟩ := List.rotate_one_eq_self_iff_eq_replicate.mp
      (Subtype.ext_iff.mp (Subtype.ext_iff.mp hv))
    exact ⟨g,by simpa only [List.Vector.toList_length] using hg⟩
  · rintro ⟨g,hg⟩
    apply Subtype.ext
    apply Subtype.ext
    change v.val.toList.rotate 1 = v.val.toList
    rw [hg,List.rotate_replicate]

end ProductOne

theorem permutation_fixed_iff {A : Type*} (σ : Equiv.Perm A) (a : A) :
    a ∈ fixedPoints (Subgroup.zpowers σ) A ↔ σ a = a := by
  constructor
  · intro ha
    exact mem_fixedPoints.mp ha ⟨σ,Subgroup.mem_zpowers σ⟩
  · intro ha
    apply mem_fixedPoints.mpr
    rintro ⟨g,hg⟩
    obtain ⟨m,rfl⟩ := hg
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self ha m

/-- C10: every rotation action has 1-or-p orbit sizes; fixed tuples are
literally constant tuples. This fact does not presume a nontrivial tuple. -/
theorem prime_rotation_orbits {A : Type*} [Finite A] {p : ℕ} [hp : Fact p.Prime]
    (σ : Equiv.Perm A) (hσ : σ ^ p = 1) (a : A) :
    Nat.card (orbit (Subgroup.zpowers σ) a) = 1 ∨
      Nat.card (orbit (Subgroup.zpowers σ) a) = p := by
  have hd : Nat.card (Subgroup.zpowers σ) ∣ p := by
    rw [Nat.card_zpowers]
    exact orderOf_dvd_of_pow_eq_one hσ
  obtain ⟨n,hn⟩ : ∃ n, Nat.card (Subgroup.zpowers σ) = p^n := by
    rcases (Nat.dvd_prime hp.out).mp hd with h | h
    · exact ⟨0,by simpa only [pow_zero] using h⟩
    · exact ⟨1,by simpa only [pow_one] using h⟩
  obtain ⟨k,hk⟩ := orbit_card_power hn a
  have hd' : Nat.card (orbit (Subgroup.zpowers σ) a) ∣ p := by
    letI := Fintype.ofFinite (Subgroup.zpowers σ)
    letI := Fintype.ofFinite (orbit (Subgroup.zpowers σ) a)
    letI := Fintype.ofFinite (stabilizer (Subgroup.zpowers σ) a)
    have ho : Nat.card (orbit (Subgroup.zpowers σ) a) ∣ Nat.card (Subgroup.zpowers σ) := by
      exact ⟨Nat.card (stabilizer (Subgroup.zpowers σ) a),by
        simpa only [Nat.card_eq_fintype_card] using
          (card_orbit_mul_card_stabilizer_eq_card_group (Subgroup.zpowers σ) a).symm⟩
    exact ho.trans hd
  exact (Nat.dvd_prime hp.out).mp hd'

/-- The local cyclic-tuple Cauchy conclusion. -/
theorem local_cauchy [Finite K] (p : ℕ) [hp : Fact p.Prime]
    (hd : p ∣ Nat.card K) : ∃ g : K, orderOf g = p := by
  classical
  letI := Fintype.ofFinite K
  letI := Fintype.ofFinite (ProductOne K p)
  have hp' : p-1 ≠ 0 := Nat.sub_ne_zero_of_lt hp.out.one_lt
  have hcount : p ∣ Nat.card (ProductOne K p) := by
    rw [ProductOne.count]
    exact hd.trans (dvd_pow (dvd_refl _) hp')
  let f := fun k (v : ProductOne K p) => ProductOne.rotate K v k
  have hf0 : ∀ v, f 0 v = v := ProductOne.rotate_zero K
  have hfadd : ∀ j k v, f k (f j v) = f (j+k) v := fun j k v => ProductOne.rotate_rotate K v j k
  have hfp : ∀ v, f p v = v := ProductOne.rotate_length K
  let σ : Equiv.Perm (ProductOne K p) :=
    ⟨f 1,f (p-1),fun v => by rw [hfadd,Nat.add_sub_cancel' hp.out.one_lt.le,hfp],
      fun v => by rw [hfadd,Nat.sub_add_cancel hp.out.one_lt.le,hfp]⟩
  have hpow : ∀ k v, (σ ^ k) v = f k v := by
    intro k
    induction k with
    | zero => exact fun v => (hf0 v).symm
    | succ k ih =>
      intro v
      rw [pow_succ,Equiv.Perm.mul_apply,ih (σ v)]
      change f k (f 1 v) = f (k+1) v
      rw [hfadd 1 k,Nat.add_comm 1 k]
  have hσ : σ ^ p = 1 := Equiv.Perm.ext (fun v => by rw [hpow,hfp]; rfl)
  have hcardσ : ∃ n, Nat.card (Subgroup.zpowers σ) = p^n := by
    have hdσ : Nat.card (Subgroup.zpowers σ) ∣ p := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hσ
    rcases (Nat.dvd_prime hp.out).mp hdσ with h | h
    · exact ⟨0,by simpa only [pow_zero] using h⟩
    · exact ⟨1,by simpa only [pow_one] using h⟩
  obtain ⟨n,hn⟩ := hcardσ
  let v0 : ProductOne K p := ⟨List.Vector.replicate p 1,by
    change (List.replicate p (1 : K)).prod = 1
    simp⟩
  have hv0 : σ v0 = v0 := Subtype.ext (Subtype.ext (List.rotate_replicate (1 : K) p 1))
  obtain ⟨v,hv,hvne⟩ := second_fixed hn hcount ((permutation_fixed_iff σ v0).mpr hv0)
  have hvrot : ProductOne.rotate K v 1 = v := (permutation_fixed_iff σ v).mp hv
  obtain ⟨g,hg⟩ := (ProductOne.rotation_fixed_iff_constant K v).mp hvrot
  refine ⟨g,orderOf_eq_prime ?_ ?_⟩
  · rw [← List.prod_replicate,← hg]
    exact v.property
  · intro hgone
    apply hvne
    apply Subtype.ext
    apply List.Vector.toList_injective
    change v.val.toList = List.replicate p (1 : K)
    rw [hg,hgone]

end CCO.FiniteFibres.Group
