import CCO.StrongExact.ThetaCycleRootFreeSegment

/-!
# C07: every finite cyclic index is reached by forward successors

For the actual finite SimpleCycle indexing API, repeated cyclic
successor from any starting vertex visits all Fin n positions, and
does so within fewer than n steps. This arithmetic bridge allows
later theta-branch arguments to choose the two root-free intervals
without informal cyclic reindexing.
-/

namespace CCO.StrongExact

/-- Exact arithmetic readout of repeated cyclic successor. -/
theorem thetaCycleAdvance_val {n : Nat} (hn : 0 < n)
    (p : Fin n) (k : Nat) :
    (thetaCycleAdvance hn p k).val = (p.val + k) % n := by
  induction k with
  | zero =>
      change p.val = (p.val + 0) % n
      simpa only [Nat.add_zero] using (Nat.mod_eq_of_lt p.isLt).symm
  | succ k ih =>
      change ((thetaCycleAdvance hn p k).val + 1) % n =
        (p.val + (k + 1)) % n
      rw [ih, Nat.mod_add_mod]
      congr 1

/-- Any position on the finite cycle is reached after a forward
run of fewer than the number of cycle vertices. -/
theorem thetaCycleAdvance_reaches {n : Nat} (hn : 0 < n)
    (p q : Fin n) :
    ∃ k : Nat, k < n ∧ thetaCycleAdvance hn p k = q := by
  by_cases hle : p.val ≤ q.val
  · refine ⟨q.val - p.val, by omega, ?_⟩
    apply Fin.ext
    rw [thetaCycleAdvance_val]
    have hsum : p.val + (q.val - p.val) = q.val := by omega
    rw [hsum]
    exact Nat.mod_eq_of_lt q.isLt
  · refine ⟨n + q.val - p.val, by omega, ?_⟩
    apply Fin.ext
    rw [thetaCycleAdvance_val]
    have hsum : p.val + (n + q.val - p.val) = n + q.val := by omega
    rw [hsum]
    simpa [Nat.add_mod, Nat.mod_eq_of_lt q.isLt]

end CCO.StrongExact
