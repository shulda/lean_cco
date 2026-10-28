import CCO.Finite
import Mathlib.Combinatorics.SimpleGraph.Basic

/-! Concrete finite graph witnesses consumed by the original orbital-parity argument. -/
namespace CCO.ParityHasse.Sparse

/-- Every positive short cyclic sequence of distinct formal vertices omits an edge. -/
def NoShortCycles {V : Type*} (G : SimpleGraph V) (g : ℕ) : Prop :=
  ∀ (ℓ : ℕ) (hℓ : 3 ≤ ℓ), ℓ ≤ g → ∀ f : Fin ℓ ↪ V,
    ¬ ∀ p, G.Adj (f p) (f (CCO.cyclicNext (by omega) p))

/-- The finite graph needed for the unlabelled parity argument. -/
structure HighGirthChromatic (q g : ℕ) where
  size : ℕ
  graph : SimpleGraph (Fin size)
  noShortCycles : NoShortCycles graph g
  monochromatic : ∀ κ : Fin size → Fin q,
    ∃ x y, graph.Adj x y ∧ κ x = κ y

end CCO.ParityHasse.Sparse
