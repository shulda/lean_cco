import CCO.Finite
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

/-!
# Finite cycle successor geometry for RAW anchored fans

For a genuine nonempty finite simple cycle, the cyclic successor
of each position is unique. Its injectivity is the combinatorial
ingredient needed to identify the two edges incident to a root.
No mathematical completion axiom is assumed.
-/

namespace CCO.RawExact

theorem cyclicNext_injective {n : Nat} (hn : 0 < n) :
    Function.Injective (cyclicNext hn) := by
  intro p q hpq
  apply Fin.ext
  have hp := p.isLt
  have hq := q.isLt
  have heq := congrArg Fin.val hpq
  change (p.val + 1) % n = (q.val + 1) % n at heq
  have hmod (r : Fin n) :
      (r.val + 1) % n =
        if r.val + 1 = n then 0 else r.val + 1 := by
    by_cases h : r.val + 1 = n
    · rw [if_pos h, h, Nat.mod_self]
    · have hlt : r.val + 1 < n := by omega
      rw [if_neg h, Nat.mod_eq_of_lt hlt]
  rw [hmod p, hmod q] at heq
  split_ifs at heq <;> omega

end CCO.RawExact
