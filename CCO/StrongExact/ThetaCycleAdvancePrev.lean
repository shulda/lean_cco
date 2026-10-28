import CCO.StrongExact.ThetaCycleIndexCover
import CCO.StrongExact.ThetaCyclicIndexInverse

/-!
# C07 finite-cycle indexed predecessor after a forward step

The predecessor of the index reached after m+1 forward steps
is exactly the index reached after m steps. This finite identity
keeps the iterative branch-rank proof typed at each cyclic index.
-/

namespace CCO.StrongExact

theorem thetaCycleAdvance_prev_succ {n : Nat}
    (hn : 0 < n) (p : Fin n) (m : Nat) :
    cyclicPrev hn (thetaCycleAdvance hn p (m + 1)) =
      thetaCycleAdvance hn p m := by
  change cyclicPrev hn
    (cyclicNext hn (thetaCycleAdvance hn p m)) =
      thetaCycleAdvance hn p m
  exact cyclicPrev_next hn (thetaCycleAdvance hn p m)

end CCO.StrongExact
