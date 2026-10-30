import CCO.FiniteFibres.Group.Normalizer

/-! Finite transitive actions retain arbitrary kernels: orbit-stabilizer and
prime-power counts require neither a faithful action nor a regular action. -/
namespace CCO.FiniteFibres.Group
open MulAction

variable {G A : Type*} [Group G] [Finite G] [MulAction G A] [Finite A]

theorem transitive_card_dvd (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A) :
    Nat.card A ∣ Nat.card G := by
  classical
  have ho : orbit G a = Set.univ := Set.eq_univ_of_forall (fun b => trans a b)
  have hc : Nat.card (orbit G a) = Nat.card A := by rw [ho]; simp
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (orbit G a)
  letI := Fintype.ofFinite (stabilizer G a)
  rw [← hc]
  refine ⟨Nat.card (stabilizer G a),?_⟩
  simpa only [Nat.card_eq_fintype_card] using
    (card_orbit_mul_card_stabilizer_eq_card_group G a).symm

/-- Independent cardinal support for a possibly nonfaithful transitive
p-group action. This does not claim that the action is free or regular. -/
theorem transitive_card_power {p n : ℕ} [hp : Fact p.Prime]
    (hG : Nat.card G = p^n) (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A) :
    ∃ m, m ≤ n ∧ Nat.card A = p^m := by
  have hd := transitive_card_dvd trans a
  rw [hG] at hd
  exact (Nat.dvd_prime_pow hp.out).mp hd

theorem transitive_card_two_power {n : ℕ} (hG : Nat.card G = 2^n)
    (trans : ∀ x y : A, ∃ g : G, g • x = y) (a : A) :
    ∃ m, Nat.card A = 2^m := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m,_,hm⟩ := transitive_card_power hG trans a
  exact ⟨m,hm⟩

/-- A faithful representation INTO a finite p-group transfers the order
conclusion. This representation need not be onto the larger group. -/
theorem card_power_of_injective_hom {H : Type*} [Group H] [Finite H]
    {p n : ℕ} [hp : Fact p.Prime] (hH : Nat.card H = p^n)
    (f : G →* H) (hf : Function.Injective f) :
    ∃ m, m ≤ n ∧ Nat.card G = p^m := by
  have hd := Subgroup.card_subgroup_dvd_card f.range
  rw [hH] at hd
  obtain ⟨m,hm,hcard⟩ := (Nat.dvd_prime_pow hp.out).mp hd
  exact ⟨m,hm,(Nat.card_congr (MulEquiv.ofInjective hf).toEquiv).trans hcard⟩

end CCO.FiniteFibres.Group
