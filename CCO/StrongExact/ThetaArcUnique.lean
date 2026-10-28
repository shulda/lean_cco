import CCO.StrongExact.ThetaCrossBranchEdges
import CCO.StrongExact.ThetaSameBranchUnique

/-!
# C07 hard theta: every ordered formal pair carries at most one old arc

For a finite family of positive word branches ALL of length at least
two, every arc in the finite theta candidate list is unique given its
literal ordered endpoints, including its genuine old atomic colour.

Within a private branch, increasing rank forbids reversed two-cycles.
Different branches cannot share both edge endpoints, because their
only common vertices are the two global roots and no long word has a
direct root-to-root letter.

This closes the local single-valuedness obligation needed to define
a B001 PartialDiagram, but does not yet claim the simple-cycle
classification or word-profile 2-Helly.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Actual uniqueness of every fully typed directed candidate arc
given only its two ORIGINAL FORMAL endpoints. -/
theorem thetaArcs_unique_of_endpoints
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (A B : ThetaArc S ws)
    (hA : A ∈ thetaArcs S ws) (hB : B ∈ thetaArcs S ws)
    (hSrc : A.src = B.src) (hDst : A.dst = B.dst) :
    A = B := by
  obtain ⟨b,e,he⟩ := thetaArc_exists_edge S ws A hA
  obtain ⟨c,f,hf⟩ := thetaArc_exists_edge S ws B hB
  by_cases hbc : b = c
  · subst c
    exact sameBranchArc_unique S ws b A B
      ⟨e,he⟩ ⟨f,hf⟩ hSrc hDst
  · exfalso
    rcases he with he | he
    · rcases hf with hf | hf
      · have hs : thetaBranchEdgeSource S ws b e =
            thetaBranchEdgeSource S ws c f := by
          simpa [he,hf,thetaForwardArc] using hSrc
        have ht : thetaBranchEdgeTarget S ws b e =
            thetaBranchEdgeTarget S ws c f := by
          simpa [he,hf,thetaForwardArc] using hDst
        exact crossBranchEdge_no_parallel S ws hLong b c hbc e f
          ⟨hs,ht⟩
      · have hs : thetaBranchEdgeSource S ws b e =
            thetaBranchEdgeTarget S ws c f := by
          simpa [he,hf,thetaForwardArc,ThetaArc.reverse] using hSrc
        have ht : thetaBranchEdgeTarget S ws b e =
            thetaBranchEdgeSource S ws c f := by
          simpa [he,hf,thetaForwardArc,ThetaArc.reverse] using hDst
        exact crossBranchEdge_no_reversed_parallel S ws hLong b c hbc e f
          ⟨hs,ht⟩
    · rcases hf with hf | hf
      · have hs : thetaBranchEdgeSource S ws b e =
            thetaBranchEdgeTarget S ws c f := by
          simpa [he,hf,thetaForwardArc,ThetaArc.reverse] using hDst
        have ht : thetaBranchEdgeTarget S ws b e =
            thetaBranchEdgeSource S ws c f := by
          simpa [he,hf,thetaForwardArc,ThetaArc.reverse] using hSrc
        exact crossBranchEdge_no_reversed_parallel S ws hLong b c hbc e f
          ⟨hs,ht⟩
      · have hs : thetaBranchEdgeSource S ws b e =
            thetaBranchEdgeSource S ws c f := by
          simpa [he,hf,thetaForwardArc,ThetaArc.reverse] using hDst
        have ht : thetaBranchEdgeTarget S ws b e =
            thetaBranchEdgeTarget S ws c f := by
          simpa [he,hf,thetaForwardArc,ThetaArc.reverse] using hSrc
        exact crossBranchEdge_no_parallel S ws hLong b c hbc e f
          ⟨hs,ht⟩

end CCO.StrongExact
