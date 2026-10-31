import CCO.TerminalLattice.SparseCycleStarSteps
import CCO.TerminalLattice.SparseWordMarkedEdges

/-!
# B050 C27: exact selected words on ordered compressed sparse-star cycles

The accepted B002 marked projection retains the ACTUAL canonical finite edge
identifiers and their cyclic endpoint order. We refine the existing support
theorems: each used edge carries precisely the original selected spoke word or
the selected WORD OF ITS TRUE W EDGE LABEL. For non-centre consecutive
vertices, we also retain their exact orientation, including reversal of a
canonical ascending marked pair.

No homomorphism or global CCO completion is assumed. This is a structural
input for turning the already verified labelled path spectra into actual
per-cycle old positive-word realizations.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- A PRESENT canonical pair has its EXACT original source word:
the last-centre spoke or the word of the genuine unordered W graph edge.
There is no word at an absent graph pair. -/
theorem oldSparseWordSelection_present_exact_word
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (e : CCO.RawExact.QuotientExpansion.Edge (W.size+1))
    (hPresent : ∃ word : PositiveWord S i i,
      oldSparseWordSelection S W spoke words e = some word) :
    (e.val.2.val = W.size ∧
      oldSparseWordSelection S W spoke words e = some spoke) ∨
    ∃ x y : Fin W.size,
      x.val = e.val.1.val ∧ y.val = e.val.2.val ∧
      W.graph.Adj x y ∧
      oldSparseWordSelection S W spoke words e =
        some (words (W.label s(x,y))) := by
  classical
  rcases oldSparseWordSelection_present_is_star_or_graph
      S W spoke words e hPresent with hCentre | ⟨x,y,hx,hy,hAdj⟩
  · left
    exact ⟨hCentre, by simp [oldSparseWordSelection,hCentre]⟩
  · right
    have hxy : x < y := by
      have hlt := e.property
      change x.val < y.val
      omega
    have he : e = oldSparseGraphMarkedEdge W x y hxy := by
      apply Subtype.ext
      apply Prod.ext
      · apply Fin.ext
        simpa [oldSparseGraphMarkedEdge,oldSparseRoot] using hx.symm
      · apply Fin.ext
        simpa [oldSparseGraphMarkedEdge,oldSparseRoot] using hy.symm
    refine ⟨x,y,hx,hy,hAdj,?_⟩
    rw [he]
    exact oldSparseWordSelection_graph S W spoke words x y hxy hAdj

/-- Every marked edge of an ACTUAL compressed cycle uses precisely its
one genuine source-positive word. The conclusion does not assume the
centre is absent or that the marked orientation is increasing. -/
theorem oldSparseWordDiagram_projected_exact_word
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
    (k : Fin B.length) :
    ((B.edges k).val.2.val = W.size ∧
      oldSparseWordSelection S W spoke words (B.edges k) = some spoke) ∨
    ∃ x y : Fin W.size,
      x.val = (B.edges k).val.1.val ∧
      y.val = (B.edges k).val.2.val ∧
      W.graph.Adj x y ∧
      oldSparseWordSelection S W spoke words (B.edges k) =
        some (words (W.label s(x,y))) := by
  let selection := oldSparseWordSelection S W spoke words
  have hUsed : CCO.RawExact.CyclicSuppression.LabelOn
      (CCO.RawExact.QuotientExpansion.initialCycle S
        (fun _ : Fin (W.size+1) => i)
        (oldOptionalPositivePresentations S selection)
        (oldOptionalPositivePresentations_nonempty S H sap selection) C)
      (B.edges k) :=
    (B.labels_iff (B.edges k)).mpr ⟨k,rfl⟩
  obtain ⟨word,hWord⟩ :=
    oldOptionalPositive_used_marked_edge_has_word
      S H sap selection C (B.edges k) hUsed
  exact oldSparseWordSelection_present_exact_word
    S W spoke words (B.edges k) ⟨word,hWord⟩

/-- The left endpoint of an ascending canonical pair can never be the
LAST marked centre. This is a literal order fact, not graph geometry. -/
theorem oldSparseMarkedEdge_left_ne_centre
    {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (e : CCO.RawExact.QuotientExpansion.Edge (W.size+1)) :
    CCO.RawExact.QuotientExpansion.left e ≠ oldSparseCentre W := by
  intro h
  have hv := congrArg Fin.val h
  have hlt := e.property
  have hr := e.val.2.isLt
  change e.val.1.val = W.size at hv
  change e.val.1.val < e.val.2.val at hlt
  omega

/-- Any actual projected cycle step INCIDENT TO the unique centre is
labelled by the exact positive OLD SPOKE word, whichever way the step
is traversed. The centre is necessarily the canonical RIGHT endpoint. -/
theorem oldSparseWordDiagram_projected_centre_step_word
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
    (hIncident : B.vertices k = oldSparseCentre W ∨
      B.vertices (CCO.cyclicNext B.length_pos k) = oldSparseCentre W) :
    oldSparseWordSelection S W spoke words (B.edges k) = some spoke := by
  have hNoLeft :=
    oldSparseMarkedEdge_left_ne_centre W (B.edges k)
  have hRight :
      CCO.RawExact.QuotientExpansion.right (B.edges k) =
        oldSparseCentre W := by
    rcases hIncident with hAt | hAfter
    · rcases B.endpoints k with ⟨hs,_⟩ | ⟨hs,_⟩
      · exact False.elim (hNoLeft (hs.symm.trans hAt))
      · exact hs.symm.trans hAt
    · rcases B.endpoints k with ⟨_,he⟩ | ⟨_,he⟩
      · exact he.symm.trans hAfter
      · exact False.elim (hNoLeft (he.symm.trans hAfter))
  have hCentre : (B.edges k).val.2.val = W.size := by
    have hv := congrArg Fin.val hRight
    simpa [CCO.RawExact.QuotientExpansion.right,oldSparseCentre] using hv
  simp [oldSparseWordSelection,hCentre]

/-- Every non-centre projected step is a REAL W edge carrying its exact
label-specific OLD word. Furthermore its two cyclic endpoint roots
are literally the two graph endpoints in one of the two orientations.
This preserves reversed traversal, instead of silently ordering all
words in the wrong direction. -/
theorem oldSparseWordDiagram_projected_graph_step_word
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
    ∃ x y : Fin W.size,
      W.graph.Adj x y ∧
      oldSparseWordSelection S W spoke words (B.edges k) =
        some (words (W.label s(x,y))) ∧
      ((B.vertices k = oldSparseRoot W x ∧
        B.vertices (CCO.cyclicNext B.length_pos k) = oldSparseRoot W y) ∨
       (B.vertices k = oldSparseRoot W y ∧
        B.vertices (CCO.cyclicNext B.length_pos k) = oldSparseRoot W x)) := by
  rcases oldSparseWordDiagram_projected_exact_word
      S H sap W spoke words C B k with
    ⟨hCentre,_⟩ | ⟨x,y,hx,hy,hAdj,hWord⟩
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
    refine ⟨x,y,hAdj,hWord,?_⟩
    rcases B.endpoints k with ⟨hStart,hEnd⟩ | ⟨hStart,hEnd⟩
    · exact Or.inl ⟨hStart.trans hLeft,hEnd.trans hRight⟩
    · exact Or.inr ⟨hStart.trans hRight,hEnd.trans hLeft⟩

end CCO.TerminalLattice
