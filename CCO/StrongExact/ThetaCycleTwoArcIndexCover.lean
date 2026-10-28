import CCO.StrongExact.ThetaCycleAdvanceReturn

/-!
# Exactly two cyclic intervals cover every simple cycle position

Two positive root-to-root successor distances sum to the full cycle
length. Moreover every cycle index lies on the first or on the
complementary second interval, with no omitted formal vertices.
The proof is pure finite arithmetic on the original Fin n indexes.
-/

namespace CCO.StrongExact

theorem thetaCycle_two_arc_lengths_add
    {n : Nat} (hn : 0 < n)
    (p q : Fin n) (k l : Nat)
    (hk : 0 < k) (hl : 0 < l)
    (hkn : k < n) (hln : l < n)
    (hForward : thetaCycleAdvance hn p k = q)
    (hBackward : thetaCycleAdvance hn q l = p) :
    k + l = n := by
  have hReturn : thetaCycleAdvance hn p (k + l) = p := by
    rw [thetaCycleAdvance_add, hForward, hBackward]
  exact thetaCycleAdvance_positive_return_length hn p k l
    hk hl hkn hln hReturn

theorem thetaCycle_two_arc_index_cover
    {n : Nat} (hn : 0 < n)
    (p q : Fin n) (k l : Nat)
    (hkn : k < n) (hln : l < n)
    (hForward : thetaCycleAdvance hn p k = q)
    (hSum : k + l = n)
    (r : Fin n) :
    (∃ m : Nat, m ≤ k ∧ thetaCycleAdvance hn p m = r) ∨
    (∃ t : Nat, t ≤ l ∧ thetaCycleAdvance hn q t = r) := by
  obtain ⟨m,hm,hReached⟩ := thetaCycleAdvance_reaches hn p r
  by_cases hSmall : m ≤ k
  · exact Or.inl ⟨m,hSmall,hReached⟩
  · let t : Nat := m - k
    have hBound : t ≤ l := by
      dsimp only [t]
      omega
    right
    refine ⟨t,hBound,?_⟩
    calc
      thetaCycleAdvance hn q t =
          thetaCycleAdvance hn (thetaCycleAdvance hn p k) t := by rw [hForward]
      _ = thetaCycleAdvance hn p (k + t) :=
          (thetaCycleAdvance_add hn p k t).symm
      _ = thetaCycleAdvance hn p m := by
          rw [show k + t = m by omega]
      _ = r := hReached

end CCO.StrongExact
