import CCO.TerminalLattice.SparseCycleNoCentre

/-!
# B050 C27: root-to-root edges in a marked cycle meeting the centre

The accepted B002 compression gives an actual injective cyclic sequence
of marked vertices. The concrete sparse-word selection has exactly ONE
last centre, and all its other marked vertices are literal vertices
of the accepted B006 sparse graph W.

For EACH projected cycle edge whose two endpoints are NOT the centre,
the endpoints are adjacent in W, preserving their ACTUAL cyclic order,
even when another edge of the same cycle goes through the centre.
The absent graph pairs and private interiors cannot become W edges.
This is the correct local step needed to extract the graph path between
the two centre spokes without assuming a global graph-cycle witness.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The inverse graph-root coordinate of any genuinely non-centre
marked point. Its bound is proved from the uniqueness of the
literal LAST centre, not from an assumed graph injection. -/
def oldSparseNonCentreRoot {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (m : Fin (W.size+1)) (h : m ≠ oldSparseCentre W) :
    Fin W.size :=
  ⟨m.val, by
    have hm := m.isLt
    have hNot : m.val ≠ W.size := by
      intro hv
      apply h
      apply Fin.ext
      simpa [oldSparseCentre] using hv
    omega⟩

/-- Each actual graph root retains its original index when viewed
inside the finite star and then restricted away from the centre. -/
theorem oldSparseNonCentreRoot_of_root {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (v : Fin W.size) :
    oldSparseNonCentreRoot W (oldSparseRoot W v)
      (oldSparseRoot_ne_centre W v) = v := by
  apply Fin.ext
  rfl

/-- C27 exact local star-support theorem. Consecutive non-centre
vertices of ANY compressed marked cycle of the ONE source diagram
are consecutive in the actual W graph, with the SAME orientation.
Only true W adjacency and B002 literal marked-edge endpoints are used. -/
theorem oldSparseWordDiagram_projected_noncentre_adjacent
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
    (k : Fin B.length)
    (hFirst : B.vertices k ≠ oldSparseCentre W)
    (hSecond : B.vertices (CCO.cyclicNext B.length_pos k) ≠
      oldSparseCentre W) :
    W.graph.Adj
      (oldSparseNonCentreRoot W (B.vertices k) hFirst)
      (oldSparseNonCentreRoot W
        (B.vertices (CCO.cyclicNext B.length_pos k)) hSecond) := by
  rcases oldSparseWordDiagram_projected_edges_star_or_graph
      S H sap W spoke words C B k with hCentre | ⟨x,y,hx,hy,hAdj⟩
  · have hRight :
        CCO.RawExact.QuotientExpansion.right (B.edges k) =
          oldSparseCentre W := by
      apply Fin.ext
      simpa [CCO.RawExact.QuotientExpansion.right,oldSparseCentre] using hCentre
    rcases B.endpoints k with ⟨_,hEnd⟩ | ⟨hStart,_⟩
    · exact False.elim (hSecond (hEnd.trans hRight))
    · exact False.elim (hFirst (hStart.trans hRight))
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
    · have hStartGraph :
          oldSparseNonCentreRoot W (B.vertices k) hFirst = x := by
        apply Fin.ext
        simpa [oldSparseNonCentreRoot,oldSparseRoot] using
          congrArg Fin.val (hStart.trans hLeft)
      have hEndGraph :
          oldSparseNonCentreRoot W
            (B.vertices (CCO.cyclicNext B.length_pos k)) hSecond = y := by
        apply Fin.ext
        simpa [oldSparseNonCentreRoot,oldSparseRoot] using
          congrArg Fin.val (hEnd.trans hRight)
      simpa [hStartGraph,hEndGraph] using hAdj
    · have hStartGraph :
          oldSparseNonCentreRoot W (B.vertices k) hFirst = y := by
        apply Fin.ext
        simpa [oldSparseNonCentreRoot,oldSparseRoot] using
          congrArg Fin.val (hStart.trans hRight)
      have hEndGraph :
          oldSparseNonCentreRoot W
            (B.vertices (CCO.cyclicNext B.length_pos k)) hSecond = x := by
        apply Fin.ext
        simpa [oldSparseNonCentreRoot,oldSparseRoot] using
          congrArg Fin.val (hEnd.trans hLeft)
      simpa [hStartGraph,hEndGraph] using W.graph.adj_symm hAdj

/-- C27: the centre, if visited by a genuine projected cycle, is
visited at exactly one cyclic position. This is a consequence of
the real marked-projection embedding, not a new star hypothesis. -/
theorem oldSparseWordDiagram_projected_centre_unique
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
    (a b : Fin B.length)
    (ha : B.vertices a = oldSparseCentre W)
    (hb : B.vertices b = oldSparseCentre W) : a = b :=
  B.vertices.injective (ha.trans hb.symm)

end CCO.TerminalLattice
