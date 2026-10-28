import CCO.StrongExact.ThetaCycleRightArcRank
import CCO.StrongExact.ThetaCycleRootDistanceBounds
import CCO.StrongExact.ThetaPrivateLeftRank

/-!
# C07: the complementary root-to-root arc also has FULL word length

At its last private point the cyclic arc reaches the common left root,
so this point has original word rank one. The right-to-left rank
induction forces its remaining distance to equal the number of
cyclic successor steps. Hence the target rank of its original
positive word equals the whole right-to-left arc length.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_right_arc_target_rank
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (q p : Fin C.length) (l : Nat)
    (hq : C.vertices q = thetaRight S ws)
    (hp : C.vertices p = thetaLeft S ws)
    (hl : l < C.length)
    (hReached : thetaCycleAdvance C.length_pos q l = p)
    (b : Fin ws.length)
    (hArc : ∀ m : Nat, 0 < m → m < l →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos q m) =
          (.inr ⟨b,t⟩ : thetaVertices S ws)) :
    wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) = l := by
  have hlTwo := thetaCycle_right_left_distance_ge_two
    S ws hLong C q p l hq hp hReached
  have hLast : 0 < l - 1 ∧ l - 1 < l := by omega
  obtain ⟨t,ht,hRank⟩ :=
    thetaCycle_right_arc_remaining_rank_matches_distance S ws hLong C
      q p l hq hp hl hReached b hArc (l - 1) hLast.1 hLast.2
  have hLastNext :
      cyclicNext C.length_pos
        (thetaCycleAdvance C.length_pos q (l - 1)) = p := by
    calc
      cyclicNext C.length_pos
        (thetaCycleAdvance C.length_pos q (l - 1)) =
          thetaCycleAdvance C.length_pos q ((l - 1) + 1) := rfl
      _ = thetaCycleAdvance C.length_pos q l := by
        rw [show (l - 1) + 1 = l by omega]
      _ = p := hReached
  have hAdjacent : thetaAdjacent S ws
      (.inr ⟨b,t⟩ : thetaVertices S ws) (thetaLeft S ws) := by
    have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices (thetaCycleAdvance C.length_pos q (l - 1)))
      (C.vertices (cyclicNext C.length_pos
        (thetaCycleAdvance C.length_pos q (l - 1))))
      (C.next_ne (thetaCycleAdvance C.length_pos q (l - 1)))).mp
        (C.specified (thetaCycleAdvance C.length_pos q (l - 1)))
    rw [ht,hLastNext,hp] at he
    exact he
  have hRankOne :=
    thetaPrivate_adj_left_rank_one S ws b t hAdjacent
  omega

end CCO.StrongExact
