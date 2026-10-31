import CCO.TerminalLattice.SparseCycleProjectionEdges

/-!
# B050 C27: a projected cycle avoiding the centre IS a genuine W cycle

The accepted B002 marked projection gives an injective cyclic sequence
of roots and true original used-edge identifiers. The verified source
C27 support lemma forces each identifier to be either a W-adjacent
graph-root pair or a centre spoke. When the centre is absent from the
cycle, every edge is a genuine W graph edge; the original cyclic
ordering is retained, not replaced by an arbitrary edge list.

This is the exact finite graph-cycle input required by the already
proved B050 C29 sparse-girth/power argument. No global old CCO,
fake graph edge, extra quotient action, or unproved connectivity
hypothesis is used.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- Every actual centre-free marked projection is a literal simple
W graph cycle: all root vertices occur in the same cyclic order,
no repeated graph vertices, and every consecutive pair is a genuine
edge of the ORIGINAL accepted sparse graph. -/
theorem oldSparseWordDiagram_centre_free_graph_cycle
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (C : SimpleCycle (oldSparseWordDiagram S H sap W spoke words))
    (B : CCO.RawExact.QuotientExpansion.MarkedProjection
      S (fun _ : Fin (W.size+1) => i)
      (oldOptionalPositivePresentations S
        (oldSparseWordSelection S W spoke words))
      (oldOptionalPositivePresentations_nonempty S H sap
        (oldSparseWordSelection S W spoke words)) C)
    (hNoCentre : ∀ k : Fin B.length,
      B.vertices k ≠ oldSparseCentre W) :
    ∃ vertices : Fin B.length ↪ Fin W.size,
      ∀ k : Fin B.length,
        W.graph.Adj (vertices k)
          (vertices (CCO.cyclicNext B.length_pos k)) := by
  let toGraph : Fin B.length → Fin W.size :=
    fun k => ⟨(B.vertices k).val, by
      have hlt := (B.vertices k).isLt
      have hneq : (B.vertices k).val ≠ W.size := by
        intro heq
        apply hNoCentre k
        apply Fin.ext
        simpa [oldSparseCentre] using heq
      omega⟩
  have hInj : Function.Injective toGraph := by
    intro x y hxy
    apply B.vertices.injective
    apply Fin.ext
    exact congrArg Fin.val hxy
  refine ⟨⟨toGraph, hInj⟩, ?_⟩
  intro k
  rcases oldSparseWordDiagram_projected_edges_star_or_graph
      S H sap W spoke words C B k with hCentre | ⟨x,y,hx,hy,hAdj⟩
  · have hRight :
        CCO.RawExact.QuotientExpansion.right (B.edges k) =
          oldSparseCentre W := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.right,oldSparseCentre] using hCentre
    rcases B.endpoints k with ⟨_,hEnd⟩ | ⟨hStart,_⟩
    · exact False.elim
        (hNoCentre (CCO.cyclicNext B.length_pos k) (hEnd.trans hRight))
    · exact False.elim (hNoCentre k (hStart.trans hRight))
  · have hLeft :
        CCO.RawExact.QuotientExpansion.left (B.edges k) =
          oldSparseRoot W x := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.left,oldSparseRoot] using hx.symm
    have hRight :
        CCO.RawExact.QuotientExpansion.right (B.edges k) =
          oldSparseRoot W y := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.right,oldSparseRoot] using hy.symm
    rcases B.endpoints k with ⟨hStart,hEnd⟩ | ⟨hStart,hEnd⟩
    · have hVstart : toGraph k = x := by
        apply Fin.ext
        exact congrArg Fin.val (hStart.trans hLeft)
      have hVend : toGraph (CCO.cyclicNext B.length_pos k) = y := by
        apply Fin.ext
        exact congrArg Fin.val (hEnd.trans hRight)
      simpa [hVstart,hVend] using hAdj
    · have hVstart : toGraph k = y := by
        apply Fin.ext
        exact congrArg Fin.val (hStart.trans hRight)
      have hVend : toGraph (CCO.cyclicNext B.length_pos k) = x := by
        apply Fin.ext
        exact congrArg Fin.val (hEnd.trans hLeft)
      simpa [hVstart,hVend] using W.graph.symm hAdj

end CCO.TerminalLattice
