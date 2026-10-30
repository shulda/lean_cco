import CCO.FiniteFibres.Group.Cauchy
import Mathlib.GroupTheory.QuotientGroup.Basic

assert_not_exists exists_prime_orderOf_dvd_card IsPGroup Sylow

/-! C12/C16–C20: prime divisors and the local finite p-group normalizer
argument. Fixed cosets are counted explicitly; no Sylow, Cauchy or normalizer
condition theorem is imported or applied. -/
namespace CCO.FiniteFibres.Group
open Subgroup MulAction QuotientGroup Equiv

theorem power_of_prime_divisors {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0)
    (hdiv : ∀ q, q.Prime → q ∣ m → q = p) : ∃ n, m = p^n := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm1 : m = 1
    · exact ⟨0,by simpa only [pow_zero] using hm1⟩
    obtain ⟨q,hq,hqm⟩ := Nat.exists_prime_and_dvd hm1
    have hqp := hdiv q hq hqm
    subst q
    obtain ⟨k,hk⟩ := hqm
    have hk0 : k ≠ 0 := by intro h; simp [h] at hk; exact hm hk
    have hkm : k < m := by
      rw [hk]
      exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk0) hp.one_lt
    obtain ⟨n,hn⟩ := ih k hkm hk0 (fun q hq hqk => hdiv q hq (hqk.trans ((show k ∣ m from ⟨p,by rw [hk,Nat.mul_comm]⟩))))
    exact ⟨n+1,by rw [hk,hn,pow_succ']⟩

theorem odd_prime_of_not_two_power {m : ℕ} (hm : m ≠ 0)
    (hpow : ¬∃ n, m = 2^n) : ∃ q, q.Prime ∧ q ∣ m ∧ q ≠ 2 := by
  by_contra h
  push_neg at h
  exact hpow (power_of_prime_divisors Nat.prime_two hm h)

variable {L : Type*} [Group L] [Finite L]
variable {p n : ℕ} [hp : Fact p.Prime]

theorem subgroup_card_power (hL : Nat.card L = p^n) (H : Subgroup L) :
    ∃ k, Nat.card H = p^k := by
  have hd := Subgroup.card_subgroup_dvd_card H
  rw [hL] at hd
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow hp.out).mp hd
  exact ⟨k,hk⟩

theorem quotient_card_power (hL : Nat.card L = p^n) (H : Subgroup L) :
    ∃ k, Nat.card (L ⧸ H) = p^k := by
  have hd := H.index_dvd_card
  rw [hL] at hd
  obtain ⟨k,_,hk⟩ := (Nat.dvd_prime_pow hp.out).mp hd
  exact ⟨k,hk⟩

/-- A fixed left coset is precisely a normalizer coset. Finiteness turns
conjugate containment into equality, rather than presupposing normality. -/
theorem fixed_coset_iff (H : Subgroup L) (x : L) :
    (x : L ⧸ H) ∈ fixedPoints H (L ⧸ H) ↔ x ∈ (normalizer (H : Set L)) := by
  constructor
  · intro hx
    have ha : ∀ {y : L ⧸ H}, y ∈ orbit H (x : L ⧸ H) → y = x := fun {_} => mem_fixedPoints'.mp hx _
    exact (inv_mem_iff (G := L)).mp (mem_normalizer_fintype fun u hu => by
      have h : (u⁻¹*x)⁻¹*x ∈ H := QuotientGroup.eq.mp (ha ⟨⟨u⁻¹,H.inv_mem hu⟩,rfl⟩)
      rw [mul_inv_rev,inv_inv] at h
      simpa only [inv_inv,SetLike.mem_coe] using h)
  · intro hx
    change ∀ u : L, u ∈ H ↔ x*u*x⁻¹ ∈ H at hx
    apply mem_fixedPoints'.mpr
    intro y
    induction y using Quotient.inductionOn' with
    | _ y =>
      rintro ⟨⟨u,hu⟩,huy⟩
      have hy : (u*x)⁻¹*y ∈ H := QuotientGroup.eq.mp huy
      exact QuotientGroup.eq.mpr ((H.inv_mem_iff).mp ((hx _).mpr
        ((H.mul_mem_cancel_left (H.inv_mem hu)).mp (by
          rw [hx] at hy
          simpa [mul_inv_rev,mul_assoc] using hy))))

def fixedCosetsEquiv (H : Subgroup L) :
    fixedPoints H (L ⧸ H) ≃ (normalizer (H : Set L)) ⧸ H.comap (normalizer (H : Set L)).subtype :=
  @subtypeQuotientEquivQuotientSubtype L (· ∈ (normalizer (H : Set L))) (_) (_)
    (· ∈ fixedPoints H (L ⧸ H)) (fun _ => (fixed_coset_iff H _).symm)
    (by
      intros
      unfold_projs
      rw [QuotientGroup.leftRel_apply (α := (normalizer (H : Set L))),QuotientGroup.leftRel_apply]
      rfl)

theorem normalizer_quotient_modEq (hL : Nat.card L = p^n) (H : Subgroup L) :
    Nat.card ((normalizer (H : Set L)) ⧸ H.comap (normalizer (H : Set L)).subtype) ≡ Nat.card (L ⧸ H) [MOD p] := by
  obtain ⟨k,hk⟩ := subgroup_card_power hL H
  rw [← Nat.card_congr (fixedCosetsEquiv H)]
  exact (fixed_card_modEq hk (L ⧸ H)).symm

/-- C18: the positive fixed-coset count is a multiple of p. -/
theorem normalizer_strict (hL : Nat.card L = p^n) (H : Subgroup L) (hH : H ≠ ⊤) :
    H < (normalizer (H : Set L)) := by
  obtain ⟨k,hk⟩ := quotient_card_power hL H
  have hk0 : k ≠ 0 := by
    intro hz
    have hi : H.index = 1 := by simpa only [hz,pow_zero] using (H.index_eq_card.trans hk)
    exact hH (H.index_eq_one.mp hi)
  have hd : p ∣ Nat.card (L ⧸ H) := by rw [hk]; exact dvd_pow_self p hk0
  have hdf : p ∣ Nat.card ((normalizer (H : Set L)) ⧸ H.comap (normalizer (H : Set L)).subtype) :=
    Nat.modEq_zero_iff_dvd.mp ((normalizer_quotient_modEq hL H).trans hd.modEq_zero_nat)
  have hpos : 0 < Nat.card ((normalizer (H : Set L)) ⧸ H.comap (normalizer (H : Set L)).subtype) := Nat.card_pos
  have hgt : 1 < Nat.card ((normalizer (H : Set L)) ⧸ H.comap (normalizer (H : Set L)).subtype) :=
    hp.out.one_lt.trans_le (Nat.le_of_dvd hpos hdf)
  apply lt_of_le_of_ne H.le_normalizer
  intro heq
  have htop : H.comap (normalizer (H : Set L)).subtype = ⊤ := by
    rw [← heq]
    exact H.subgroupOf_self
  rw [htop] at hgt
  simp at hgt

theorem maximal_normal (hL : Nat.card L = p^n) (H : Subgroup L) (hH : H ≠ ⊤)
    (hmax : ∀ J : Subgroup L, H < J → J = ⊤) : H.Normal :=
  Subgroup.normalizer_eq_top_iff.mp (hmax _ (normalizer_strict hL H hH))

/-- C20: maximality is an ordinary subgroup condition; the actual quotient
Cauchy witness would create an intermediate subgroup if its order exceeded p. -/
theorem maximal_index (hL : Nat.card L = p^n) (H : Subgroup L) (hH : H ≠ ⊤)
    (hmax : ∀ J : Subgroup L, H < J → J = ⊤) : H.index = p := by
  letI : H.Normal := maximal_normal hL H hH hmax
  obtain ⟨k,hk⟩ := quotient_card_power hL H
  have hk0 : k ≠ 0 := by
    intro hz
    exact hH (H.index_eq_one.mp (by simpa only [hz,pow_zero] using (H.index_eq_card.trans hk)))
  have hd : p ∣ Nat.card (L ⧸ H) := by rw [hk]; exact dvd_pow_self p hk0
  obtain ⟨g,hg⟩ := local_cauchy (L ⧸ H) p hd
  let J : Subgroup (L ⧸ H) := Subgroup.zpowers g
  have hJcard : Nat.card J = p := (Nat.card_zpowers g).trans hg
  have hJbot : J ≠ ⊥ := by
    intro h
    rw [h,Nat.card_eq_fintype_card] at hJcard
    simpa using hp.out.ne_one hJcard.symm
  let φ := QuotientGroup.mk' H
  have hsurj : Function.Surjective φ := QuotientGroup.mk'_surjective H
  have hle : H ≤ J.comap φ := by
    intro x hx
    change φ x ∈ J
    have hφ : φ x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    exact hφ.symm ▸ J.one_mem
  have hne : H ≠ J.comap φ := by
    intro he
    apply hJbot
    apply Subgroup.comap_injective hsurj
    rw [MonoidHom.comap_bot]
    change J.comap φ = (QuotientGroup.mk' H).ker
    rw [QuotientGroup.ker_mk']
    exact he.symm
  have hJtop : J = ⊤ := by
    apply Subgroup.comap_injective hsurj
    rw [Subgroup.comap_top]
    exact hmax _ (lt_of_le_of_ne hle hne)
  rw [hJtop,Subgroup.card_top] at hJcard
  exact hJcard

end CCO.FiniteFibres.Group
