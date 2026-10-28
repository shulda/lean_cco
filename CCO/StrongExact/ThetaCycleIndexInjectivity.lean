import CCO.StrongExact.ThetaCycleIndexCover

/-!
# C07: no repeated cyclic index in fewer than n forward steps

The forward successor action on Fin n has exactly one period of
length n. In particular two different steps k,l<n from the same
start vertex cannot collide. This lets the later theta proof
identify exactly the two root-to-root arcs with no hidden root.
-/

namespace CCO.StrongExact

private theorem mod_of_less_than_twice {n x : Nat}
    (hn : 0 < n) (hx : x < n + n) :
    x % n = if x < n then x else x - n := by
  by_cases h : x < n
  · simp [h, Nat.mod_eq_of_lt h]
  · have hge : n ≤ x := by omega
    have hsub : x - n < n := by omega
    simp only [if_neg h]
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hsub]

/-- Every initial segment of length less than n of a cyclic orbit
is injective. No graph or source assumptions are needed. -/
theorem thetaCycleAdvance_injective_lt
    {n : Nat} (hn : 0 < n) (p : Fin n)
    (k l : Nat) (hk : k < n) (hl : l < n)
    (heq : thetaCycleAdvance hn p k = thetaCycleAdvance hn p l) :
    k = l := by
  have hv : (p.val + k) % n = (p.val + l) % n := by
    have h := congrArg Fin.val heq
    simpa only [thetaCycleAdvance_val] using h
  have hkBound : p.val + k < n + n := by omega
  have hlBound : p.val + l < n + n := by omega
  rw [mod_of_less_than_twice hn hkBound,
      mod_of_less_than_twice hn hlBound] at hv
  split_ifs at hv <;> omega

end CCO.StrongExact
