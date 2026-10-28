import CCO.StrongExact.ThetaPrivateDegree
import CCO.StrongExact.ThetaGraphBridge
import CCO.StrongExact.ThetaCyclicIndex

/-!
# C07: local shape of genuine simple cycles at private theta vertices

At any private vertex of a specified simple cycle, its predecessor
and successor in the cycle are different (cycle length at least three).
Both are old theta edges and hence must lie on the SAME original
positive-word branch, one rank below and the other rank above.

This is a kernel-checkable local cycle constraint; it does not
declare or assume that the complete cycle traverses two whole
private branches. That global classification remains separate.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_private_two_sided
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (b : Fin ws.length)
    (inner : wordInterior S (ws.get b))
    (hHere : C.vertices p = (.inr ⟨b,inner⟩ : thetaVertices S ws)) :
    ∃ q r : wordPositions S (ws.get b),
      C.vertices (cyclicNext C.length_pos p) =
        thetaBranchPosition S ws b q ∧
      C.vertices (cyclicPrev C.length_pos p) =
        thetaBranchPosition S ws b r ∧
      ((wordPositionRank S (ws.get b) q =
            wordPositionRank S (ws.get b) inner.val + 1 ∧
        wordPositionRank S (ws.get b) inner.val =
            wordPositionRank S (ws.get b) r + 1) ∨
       (wordPositionRank S (ws.get b) inner.val =
            wordPositionRank S (ws.get b) q + 1 ∧
        wordPositionRank S (ws.get b) r =
            wordPositionRank S (ws.get b) inner.val + 1)) := by
  let prev : Fin C.length := cyclicPrev C.length_pos p
  have hNext :
      thetaAdjacent S ws (C.vertices p)
        (C.vertices (cyclicNext C.length_pos p)) := by
    exact (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
      (C.next_ne p)).mp (C.specified p)
  have hPrevDirected :
      thetaAdjacent S ws (C.vertices prev) (C.vertices p) := by
    have hEdge :=
      (thetaEdgesOfLong_edge_iff_arc S ws hLong
        (C.vertices prev)
        (C.vertices (cyclicNext C.length_pos prev))
        (C.next_ne prev)).mp (C.specified prev)
    simpa only [prev, cyclicNext_prev] using hEdge
  have hPrev :
      thetaAdjacent S ws (C.vertices p) (C.vertices prev) :=
    thetaAdjacent_symmetric S ws hPrevDirected
  have hDifferent : C.vertices (cyclicNext C.length_pos p) ≠
      C.vertices prev := by
    intro h
    have hidx : prev = cyclicNext C.length_pos p :=
      C.vertices.injective h.symm
    exact (cyclicPrev_ne_next C.length_ge_three p) hidx
  rw [hHere] at hNext hPrev
  exact thetaPrivate_distinct_neighbor_directions S ws b inner
    (C.vertices (cyclicNext C.length_pos p))
    (C.vertices prev) hNext hPrev hDifferent

end CCO.StrongExact
