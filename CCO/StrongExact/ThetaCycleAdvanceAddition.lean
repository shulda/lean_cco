import CCO.StrongExact.ThetaCycleIndexCover

/-!
# Finite cyclic advance is an associative successor action

Two successive stretches of an actual finite cycle can be combined
without choosing a cyclic starting index or inventing a new graph
vertex. This will allow the two root-to-root intervals to cover
the entire simple theta cycle.
-/

namespace CCO.StrongExact

theorem thetaCycleAdvance_add {n : Nat}
    (hn : 0 < n) (p : Fin n) (k l : Nat) :
    thetaCycleAdvance hn p (k + l) =
      thetaCycleAdvance hn (thetaCycleAdvance hn p k) l := by
  induction l with
  | zero => rfl
  | succ l ih =>
      change cyclicNext hn (thetaCycleAdvance hn p (k + l)) =
        cyclicNext hn (thetaCycleAdvance hn
          (thetaCycleAdvance hn p k) l)
      exact congrArg (cyclicNext hn) ih

end CCO.StrongExact
