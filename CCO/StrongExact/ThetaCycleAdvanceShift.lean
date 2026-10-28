import CCO.StrongExact.ThetaCycleIndexCover

/-!
# C07 cyclic successor arithmetic: shifting the start index

Starting at the next vertex and advancing k steps agrees exactly
with advancing k+1 steps from the original start. No overflow
assumption is needed because both sides use Fin n.
-/

namespace CCO.StrongExact

theorem thetaCycleAdvance_from_next {n : Nat}
    (hn : 0 < n) (p : Fin n) (k : Nat) :
    thetaCycleAdvance hn (cyclicNext hn p) k =
      thetaCycleAdvance hn p (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change cyclicNext hn (thetaCycleAdvance hn (cyclicNext hn p) k) =
        cyclicNext hn (thetaCycleAdvance hn p (k + 1))
      exact congrArg (cyclicNext hn) ih

end CCO.StrongExact
