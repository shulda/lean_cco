import CCO.Finite
import Mathlib.Tactic.Omega

/-!
# Finite genuine simple-cycle index predecessors

The accepted CCO cycle API uses `cyclicNext` on `Fin n` with
n≥3. A predecessor is needed to inspect both distinct neighbors
of an arbitrary cycle vertex, before applying theta's private
degree-two lemma. This is elementary finite arithmetic, independent
of CCO, SAP, exact menus and original colours.
-/

namespace CCO.StrongExact

/-- Literal predecessor on a positive finite cyclic ordinal. -/
def cyclicPrev {n : Nat} (hn : 0 < n) (p : Fin n) : Fin n :=
  if h0 : p.val = 0
    then ⟨n - 1, by omega⟩
    else ⟨p.val - 1, by omega⟩

theorem cyclicNext_prev {n : Nat} (hn : 0 < n) (p : Fin n) :
    cyclicNext hn (cyclicPrev hn p) = p := by
  apply Fin.ext
  change ((cyclicPrev hn p).val + 1) % n = p.val
  by_cases h0 : p.val = 0
  · have hp : (cyclicPrev hn p).val = n - 1 := by
      simp [cyclicPrev, h0]
    rw [hp]
    have hn1 : n - 1 + 1 = n := by omega
    rw [hn1, Nat.mod_self]
    exact h0.symm
  · have hp : (cyclicPrev hn p).val = p.val - 1 := by
      simp [cyclicPrev, h0]
    rw [hp]
    have hstep : p.val - 1 + 1 = p.val := by omega
    rw [hstep, Nat.mod_eq_of_lt p.isLt]

/-- In a genuine simple cycle of length at least three, the two
formal cyclic neighbors of a position are distinct. This prevents
a degenerate two-cycle from being used in theta classification. -/
theorem cyclicPrev_ne_next {n : Nat} (hn3 : 3 ≤ n) (p : Fin n) :
    cyclicPrev (by omega : 0 < n) p ≠
      cyclicNext (by omega : 0 < n) p := by
  let hn : 0 < n := by omega
  change cyclicPrev hn p ≠ cyclicNext hn p
  intro h
  have hv := congrArg Fin.val h
  by_cases h0 : p.val = 0
  · have hp : (cyclicPrev hn p).val = n - 1 := by
      simp [cyclicPrev, h0]
    have hnext : (cyclicNext hn p).val = 1 := by
      change (p.val + 1) % n = 1
      rw [h0]
      simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
    rw [hp,hnext] at hv
    omega
  · by_cases hlow : p.val + 1 < n
    · have hp : (cyclicPrev hn p).val = p.val - 1 := by
        simp [cyclicPrev, h0]
      have hnext : (cyclicNext hn p).val = p.val + 1 := by
        change (p.val + 1) % n = p.val + 1
        exact Nat.mod_eq_of_lt hlow
      rw [hp,hnext] at hv
      omega
    · have hlast : p.val + 1 = n := by omega
      have hp : (cyclicPrev hn p).val = p.val - 1 := by
        simp [cyclicPrev, h0]
      have hnext : (cyclicNext hn p).val = 0 := by
        change (p.val + 1) % n = 0
        rw [hlast]
        exact Nat.mod_self n
      rw [hp,hnext] at hv
      omega

end CCO.StrongExact
