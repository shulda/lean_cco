import CCO.StrongExact.ThetaCycleRootNeighbors
import CCO.StrongExact.ThetaPrivateLeftRank

/-! The two cyclic neighbors of the LEFT shared theta root belong to
different original positive-word occurrences. No real-point gluing
or semantic completion is assumed in this finite graph argument. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_left_neighbor_branches_distinct
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (hp : C.vertices p = thetaLeft S ws)
    (b c : Fin ws.length)
    (t : wordInterior S (ws.get b))
    (u : wordInterior S (ws.get c))
    (hNext : C.vertices (cyclicNext C.length_pos p) =
      (.inr ⟨b,t⟩ : thetaVertices S ws))
    (hPrev : C.vertices (cyclicPrev C.length_pos p) =
      (.inr ⟨c,u⟩ : thetaVertices S ws)) :
    b ≠ c := by
  intro hbc
  subst c
  have hNextAdj : thetaAdjacent S ws
      (.inr ⟨b,t⟩ : thetaVertices S ws) (thetaLeft S ws) := by
    have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
      (C.next_ne p)).mp (C.specified p)
    apply thetaAdjacent_symmetric S ws
    simpa only [hp,hNext] using he
  have hPrevAdj : thetaAdjacent S ws
      (.inr ⟨b,u⟩ : thetaVertices S ws) (thetaLeft S ws) := by
    let prev := cyclicPrev C.length_pos p
    have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices prev)
      (C.vertices (cyclicNext C.length_pos prev))
      (C.next_ne prev)).mp (C.specified prev)
    have hAtRoot : thetaAdjacent S ws
        (C.vertices prev) (C.vertices p) := by
      simpa only [prev, cyclicNext_prev] using he
    change thetaAdjacent S ws (C.vertices (cyclicPrev C.length_pos p)) (C.vertices p) at hAtRoot
    rw [hPrev, hp] at hAtRoot
    exact hAtRoot
  have hRankT := thetaPrivate_adj_left_rank_one S ws b t hNextAdj
  have hRankU := thetaPrivate_adj_left_rank_one S ws b u hPrevAdj
  have hSamePos : t = u := by
    apply Subtype.ext
    apply (wordPositionRank_injective S (ws.get b))
    exact hRankT.trans hRankU.symm
  have hCyclePair : C.vertices (cyclicNext C.length_pos p) =
      C.vertices (cyclicPrev C.length_pos p) := by
    rw [hNext, hPrev, hSamePos]
  have hIndex := C.vertices.injective hCyclePair
  exact (cyclicPrev_ne_next C.length_ge_three p) hIndex.symm

end CCO.StrongExact
