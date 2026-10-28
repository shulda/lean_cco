import Mathlib.Data.Nat.ModEq
import CCO.StrongExact.ThetaCycleAdvanceAddition

/-!
# A complete finite cycle has exact positive return length

If the finite cyclic-successor action starts at p and returns to p
after k+l positive steps, with each of k,l strictly below the
total cycle length, then the combined return occurs after exactly
the cycle length. This pure modular arithmetic is the missing
coverage invariant for the two root-to-root theta intervals.
-/

namespace CCO.StrongExact

theorem thetaCycleAdvance_positive_return_length {n : Nat}
    (hn : 0 < n) (p : Fin n)
    (k l : Nat) (hk : 0 < k) (hl : 0 < l)
    (hkn : k < n) (hln : l < n)
    (hReturn : thetaCycleAdvance hn p (k + l) = p) :
    k + l = n := by
  have hMod : (p.val + (k + l)) % n = p.val := by
    have h := congrArg Fin.val hReturn
    simpa only [thetaCycleAdvance_val] using h
  have hEq : Nat.ModEq n (p.val + (k + l)) (p.val + 0) := by
    change (p.val + (k + l)) % n = (p.val + 0) % n
    simpa only [Nat.add_zero, Nat.mod_eq_of_lt p.isLt] using hMod
  have hZero : (k + l) % n = 0 := by
    have hCancel := Nat.ModEq.add_left_cancel' p.val hEq
    change (k + l) % n = 0 % n at hCancel
    simpa only [Nat.zero_mod] using hCancel
  have hPos : 0 < k + l := by omega
  have hBound : k + l < n + n := by omega
  by_cases hSmall : k + l < n
  · rw [Nat.mod_eq_of_lt hSmall] at hZero
    omega
  · have hGe : n ≤ k + l := by omega
    have hRem : k + l - n < n := by omega
    rw [Nat.mod_eq_sub_mod hGe, Nat.mod_eq_of_lt hRem] at hZero
    omega

end CCO.StrongExact
