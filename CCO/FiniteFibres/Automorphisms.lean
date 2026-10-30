import CCO.FiniteFibres.Bipartite
import CCO.FiniteFibres.Group.Normalizer
import Mathlib.GroupTheory.GroupAction.Period

/-! The full ACTUAL finite target automorphism group has 2-power order.
Only its literal permutation faithfulness supplies a moved point. All other
generic action statements retain their nonfaithful scope. -/
namespace CCO.FiniteFibres
variable {C : Type*} (T : Target C)

theorem orbit_edge (g : Aut T) (x : Fin T.size) (a : C)
    (h : T.edge x (g • x) = some a) (n : Nat) :
    (atomGraph T a).Adj ((g^n) • x) ((g^(n+1)) • x) := by
  change T.edge ((g^n) • x) ((g^(n+1)) • x) = some a
  rw [pow_succ,mul_smul,aut_edge]
  exact h

def orbitWalk (g : Aut T) (x : Fin T.size) (a : C)
    (h : T.edge x (g • x) = some a) :
    (n : Nat) → (atomGraph T a).Walk x ((g^n) • x)
  | 0 => by simpa only [pow_zero,one_smul] using (SimpleGraph.Walk.nil : (atomGraph T a).Walk x x)
  | n+1 => (orbitWalk g x a h n).concat (orbit_edge T g x a h n)

@[simp] theorem orbitWalk_length (g : Aut T) (x : Fin T.size) (a : C)
    (h : T.edge x (g • x) = some a) (n : Nat) : (orbitWalk T g x a h n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [orbitWalk,SimpleGraph.Walk.length_concat,ih]

/-- Faithfulness is used here, for actual permutations only. -/
theorem moved_point {g : Aut T} (h : g ≠ 1) : ∃ x : Fin T.size, g • x ≠ x := by
  classical
  by_contra hn
  push_neg at hn
  apply h
  apply Subtype.ext
  apply Equiv.ext
  exact hn

theorem odd_order_impossible (cco : SemanticCCO T) (g : Aut T)
    (p : Nat) (hp : p.Prime) (hodd : Odd p) (horder : orderOf g = p) : False := by
  classical
  have hne : g ≠ 1 := by
    intro h
    have h1 : p = 1 := by simpa only [h,orderOf_one] using horder.symm
    exact hp.ne_one h1
  obtain ⟨x,hmove⟩ := moved_point T hne
  obtain ⟨a,ha⟩ := T.complete x (g • x) (Ne.symm hmove)
  have hpow : g^p = 1 := by rw [←horder]; exact pow_orderOf_eq_one g
  let closed : (atomGraph T a).Walk x x :=
    (orbitWalk T g x a ha p).copy rfl (by rw [hpow,one_smul])
  have hlen : closed.length = p := by
    dsimp only [closed]
    rw [SimpleGraph.Walk.length_copy]
    exact orbitWalk_length T g x a ha p
  exact no_odd_atom_walk T cco a x closed (hlen.symm ▸ hodd)

/-- `cor:twogroup`, retaining the inherited SYMMETRIC complete-atomic scope.
No homogeneity, transitivity, connectedness or SAP is assumed. -/
theorem automorphism_two_group (cco : SemanticCCO T) :
    ∃ k : Nat, Nat.card (Aut T) = 2^k := by
  apply Group.power_of_prime_divisors (by decide : Nat.Prime 2) (Nat.card_pos.ne')
  intro p hp hd
  by_contra hne
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g,hg⟩ := Group.local_cauchy (Aut T) p hd
  exact odd_order_impossible T cco g p hp (hp.odd_of_ne_two hne) hg

/-- C13: a prime-order moved point has the FULL p-point orbit. -/
theorem moved_prime_period (g : Aut T) (p : Nat) (hp : p.Prime)
    (horder : orderOf g = p) (x : Fin T.size) (hmove : g • x ≠ x) :
    MulAction.period g x = p := by
  have hd : MulAction.period g x ∣ p := horder ▸ MulAction.period_dvd_orderOf g x
  rcases (Nat.dvd_prime hp).mp hd with h1 | heq
  · exact (hmove (MulAction.period_eq_one_iff.mp h1)).elim
  · exact heq

theorem moved_prime_orbit_injective (g : Aut T) (p : Nat) (hp : p.Prime)
    (horder : orderOf g = p) (x : Fin T.size) (hmove : g • x ≠ x) :
    Function.Injective (fun k : Fin p => (g^k.val) • x) := by
  have hper := moved_prime_period T g p hp horder x hmove
  have hle : ∀ i j : Fin p, i.val ≤ j.val → (g^i.val) • x = (g^j.val) • x → i = j := by
    intro i j hij heq
    have hfixed : (g^(j.val-i.val)) • x = x := by
      apply MulAction.injective (g^i.val)
      change (g^i.val) • ((g^(j.val-i.val)) • x) = (g^i.val) • x
      rw [←mul_smul,←pow_add,Nat.add_sub_of_le hij]
      exact heq.symm
    have hd : p ∣ j.val-i.val := by
      have hd' := MulAction.pow_smul_eq_iff_period_dvd.mp hfixed
      simpa only [hper] using hd'
    have hz : j.val-i.val = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    apply Fin.ext
    omega
  intro i j heq
  by_cases h : i.val ≤ j.val
  · exact hle i j h heq
  · exact (hle j i (by omega) heq.symm).symm

end CCO.FiniteFibres
