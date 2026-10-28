import CCO.StrongExact.ThetaCyclicIndex

/-! The cyclic successor and predecessor are two-sided inverse
permutations of every positive finite cycle ordinal, including all
boundary positions. -/

namespace CCO.StrongExact

theorem cyclicPrev_next {n : Nat} (hn : 0 < n) (p : Fin n) :
    cyclicPrev hn (cyclicNext hn p) = p := by
  apply Fin.ext
  have hmod : (cyclicNext hn p).val = (p.val + 1) % n := rfl
  by_cases hlast : p.val + 1 = n
  · have hnext : (cyclicNext hn p).val = 0 := by
      rw [hmod, hlast, Nat.mod_self]
    have hprev : (cyclicPrev hn (cyclicNext hn p)).val = n - 1 := by
      simp [cyclicPrev, hnext]
    rw [hprev]
    omega
  · have hlt : p.val + 1 < n := by omega
    have hnext : (cyclicNext hn p).val = p.val + 1 := by
      rw [hmod]
      exact Nat.mod_eq_of_lt hlt
    have hpos : (cyclicNext hn p).val ≠ 0 := by omega
    have hprev : (cyclicPrev hn (cyclicNext hn p)).val =
        (cyclicNext hn p).val - 1 := by
      simp [cyclicPrev, hpos]
    rw [hprev, hnext]
    omega

end CCO.StrongExact
