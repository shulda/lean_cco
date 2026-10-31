import CCO.TerminalLattice.LongCycleCounting
import CCO.ParityHasse.Sparse.Labelled

/-!
# B050 C29: apply the verified sparse graph GIRTH to label multiplicity

The source I03 graph is a real simple graph with r ACTUAL edge labels,
all encoded on unordered edges. An injective cyclic ordering of m
vertices witnessing a simple graph cycle has m>r*(N-1)+1 under the
given old girth guard.

Deleting ANY chosen closing edge then leaves at least N edges of one
label on the complementary simple path. This directly connects the
source's exact finite girth and pigeonhole contracts; it does not
assert any STRONG spectrum equality, cycle completion, or CCO map yet.
-/

namespace CCO.TerminalLattice

/-- A genuine simple cycle in the ACCEPTED sparse labelled graph
retains enough occurrences of one label on its complementary path,
with ANY closing edge fixed in advance. Unlike an abstract list
pigeonhole, this consumes the actual I03 graph's NoShortCycles
contract and its unordered-edge label map. -/
theorem originalSparseGraph_complementary_label_threshold
    {q r g N m : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (hGirth : r*(N-1)+1 ≤ g)
    (hm : 3 ≤ m)
    (vertices : Fin m ↪ Fin W.size)
    (hEdges : ∀ p : Fin m,
      W.graph.Adj (vertices p)
        (vertices (CCO.cyclicNext (by omega : 0 < m) p)))
    (closing : Fin m) :
    ∃ i : Fin r,
      N ≤ finiteLabelCount
        ((Finset.univ : Finset (Fin m)).erase closing)
        (fun p : Fin m =>
          W.label s(vertices p, vertices (CCO.cyclicNext (by omega : 0 < m) p))) i := by
  have hLong : r*(N-1)+1 < m := by
    by_contra h
    have hmShort : m ≤ g := by omega
    exact (W.noShortCycles m hm hmShort vertices) hEdges
  exact long_cycle_delete_any_closing_edge
    (fun p : Fin m =>
      W.label s(vertices p, vertices (CCO.cyclicNext (by omega : 0 < m) p)))
    hLong closing

end CCO.TerminalLattice
