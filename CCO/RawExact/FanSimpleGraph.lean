import CCO.RawExact.PrivateFanSimple
import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# B002 C12/C26: actual finite private RAW fan as a SimpleGraph

The graph is built from the already checked disjoint-occurrence
private path vertices and their root/old-centre identifications.
Symmetry and irreflexivity are THEOREMS, not assumptions.
Consequently Mathlib's simple-graph cycle and path technology
can be applied to the raw fan without introducing fake parallel
edges, two-cycles or diagonal equality edges.

This is only the uncoloured skeleton: the old typed diversity
atom label of every specified edge is a separate C12 obligation.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {root : ι} {I : Type (max u v)} [Finite I]
variable {sort : I → ι}

/-- Concrete simple graph carrying exactly the old-centre and
per-occurrence private-word edges, with no other adjacency. -/
def privateFanSimpleGraph
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t)) :
    SimpleGraph (PrivateFanVertex S D centres) where
  Adj := privateFanAdjacent S D centres
  symm.symm := by
    intro v w h
    exact (privateFanAdjacent_symm S D centres v w).mp h
  loopless.irrefl := by
    intro v
    exact privateFanAdjacent_irrefl S D centres v

theorem privateFanSimpleGraph_adj_iff
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (v w : PrivateFanVertex S D centres) :
    (privateFanSimpleGraph S D centres).Adj v w ↔
      privateFanAdjacent S D centres v w :=
  Iff.rfl

end CCO.RawExact
