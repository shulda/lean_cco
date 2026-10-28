import CCO.StrongExact.ThetaCycleArcRank
import CCO.StrongExact.ThetaPrivateRightRank
import CCO.StrongExact.ThetaCycleRootDistanceBounds

/-!
# C07: the first theta root-to-root arc traverses the FULL word length

The actual right-root adjacency of the last private arc vertex
forces its word position to have penultimate rank. Combined with
the proved forward rank induction, the right root occurs after
exactly the original word's full target rank. The old colours and
named sorts are untouched; this is only finite graph geometry.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_left_arc_target_rank
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p q : Fin C.length) (k : Nat)
    (hp : C.vertices p = thetaLeft S ws)
    (hq : C.vertices q = thetaRight S ws)
    (hk : k < C.length)
    (hReached : thetaCycleAdvance C.length_pos p k = q)
    (b : Fin ws.length)
    (hArc : ∀ m : Nat, 0 < m → m < k →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos p m) =
          (.inr ⟨b,t⟩ : thetaVertices S ws)) :
    wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) = k := by
  have hkTwo := thetaCycle_left_right_distance_ge_two
    S ws hLong C p q k hp hq hReached
  have hLast : 0 < k - 1 ∧ k - 1 < k := by omega
  obtain ⟨t,ht,hRank⟩ :=
    thetaCycle_left_arc_rank_matches_distance S ws hLong C
      p q k hp hq hk hReached b hArc (k - 1) hLast.1 hLast.2
  have hLastNext :
      cyclicNext C.length_pos
        (thetaCycleAdvance C.length_pos p (k - 1)) = q := by
    calc
      cyclicNext C.length_pos
        (thetaCycleAdvance C.length_pos p (k - 1)) =
          thetaCycleAdvance C.length_pos p ((k - 1) + 1) := rfl
      _ = thetaCycleAdvance C.length_pos p k := by
        rw [show (k - 1) + 1 = k by omega]
      _ = q := hReached
  have hAdjacent : thetaAdjacent S ws
      (.inr ⟨b,t⟩ : thetaVertices S ws) (thetaRight S ws) := by
    have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices (thetaCycleAdvance C.length_pos p (k - 1)))
      (C.vertices (cyclicNext C.length_pos
        (thetaCycleAdvance C.length_pos p (k - 1))))
      (C.next_ne (thetaCycleAdvance C.length_pos p (k - 1)))).mp
        (C.specified (thetaCycleAdvance C.length_pos p (k - 1)))
    rw [ht,hLastNext,hq] at he
    exact he
  have hPenultimate :=
    thetaPrivate_adj_right_rank_pred S ws b t hAdjacent
  omega

end CCO.StrongExact
