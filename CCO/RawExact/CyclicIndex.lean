import CCO.Finite
import Mathlib.Tactic

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
  omega

end CCO.RawExact
