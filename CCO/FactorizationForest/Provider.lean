import AlgebraicAutomata.FactorizationForest.Tree

/-!
# Finite-semigroup factorization forests

The upstream formalization is by Re'em Melamed-Katz, Apache-2.0; its exact
pin, preserved notices and receiving compatibility port are recorded in
`vendor/factorization-forest/PROVENANCE.json` and `LICENSE`.

This facade keeps the exact arbitrary-semigroup theorem, including nonempty
append multiplicativity and the bound `3 * card S - 1`. The typed zero-semigroup,
ordered interval conversion and nonzero-interval discharge for B058 are separate.
-/

namespace CCO.FactorizationForest

/-- The pinned finite-semigroup forest theorem, with its original hypotheses. -/
theorem classical_bound {A S : Type*} [Semigroup S] [Fintype S] [Nonempty S]
    (eval : List A → S)
    (hmul : ∀ u v, u ≠ [] → v ≠ [] → eval (u ++ v) = eval u * eval v)
    (u : List A) (hu : u ≠ []) :
    ∃ t : FactorizationTree A,
      t.value = u ∧ t.IsRamsey eval ∧ t.height ≤ 3 * Fintype.card S - 1 :=
  factorization_forest_classical_bound eval hmul u hu

end CCO.FactorizationForest
