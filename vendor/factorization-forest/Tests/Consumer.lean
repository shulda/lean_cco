import AlgebraicAutomata.FactorizationForest.Tree

/-! Isolated provider-consumer check. This is advance dependency preparation,
not an adapter for CCO's S_typ or a completed B058 source instance. -/

example {A S : Type*} [Semigroup S] [Fintype S] [Nonempty S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧ t.IsRamsey eval ∧ t.height ≤ 3 * Fintype.card S - 1 :=
  factorization_forest_classical_bound eval hmul u hu

#check factorization_forest_classical_bound
#print axioms factorization_forest_classical_bound
#check FactorizationTree.tree_value_ne_nil
#check FactorizationTree.isRamsey_idempotent
