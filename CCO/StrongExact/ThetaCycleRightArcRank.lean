import CCO.StrongExact.ThetaCycleSecondArc
import CCO.StrongExact.ThetaCycleAdvancePrev
import CCO.StrongExact.ThetaCycleOrientation
import CCO.StrongExact.ThetaPrivateRightRank

/-!
# C07: remaining word rank along the right-to-left theta arc

The right root is the literal target of each positive branch.
The first private vertex has rank targetRank-1, and the local
two-sided cycle orientation forces subsequent original line ranks
to decrease by one. Hence after m forward cyclic steps from the
right root, the remaining word rank equals m.

This is a pure original-typed finite-cycle theorem; it does not
assume any new CCO/Helly or SAP provider.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_right_arc_remaining_rank_matches_distance
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
    ∀ m : Nat, 0 < m → m < l →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos q m) =
          (.inr ⟨b,t⟩ : thetaVertices S ws) ∧
        wordPositionRank S (ws.get b) t.val + m =
          wordPositionRank S (ws.get b)
            (wordTarget S (ws.get b)) := by
  have hGo : ∀ n : Nat, n + 1 < l →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos q (n + 1)) =
          (.inr ⟨b,t⟩ : thetaVertices S ws) ∧
        wordPositionRank S (ws.get b) t.val + (n + 1) =
          wordPositionRank S (ws.get b)
            (wordTarget S (ws.get b)) ∧
        (∃ r : wordPositions S (ws.get b),
          C.vertices (cyclicPrev C.length_pos
            (thetaCycleAdvance C.length_pos q (n + 1))) =
              thetaBranchPosition S ws b r ∧
          wordPositionRank S (ws.get b) r =
            wordPositionRank S (ws.get b) t.val + 1) := by
    intro n
    induction n with
    | zero =>
        intro hn
        obtain ⟨t,ht⟩ := hArc 1 (by omega) (by omega)
        have htNext : C.vertices (cyclicNext C.length_pos q) =
            (.inr ⟨b,t⟩ : thetaVertices S ws) := by
          simpa only [thetaCycleAdvance] using ht
        have hAdj : thetaAdjacent S ws
            (.inr ⟨b,t⟩ : thetaVertices S ws)
            (thetaRight S ws) := by
          have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
            (C.vertices q) (C.vertices (cyclicNext C.length_pos q))
            (C.next_ne q)).mp (C.specified q)
          apply thetaAdjacent_symmetric S ws
          rw [hq,htNext] at he
          exact he
        have hRank := thetaPrivate_adj_right_rank_pred S ws b t hAdj
        refine ⟨t,ht,hRank,wordTarget S (ws.get b),?_,?_⟩
        · rw [thetaCycleAdvance_prev_succ C.length_pos q 0]
          change C.vertices q =
            thetaBranchPosition S ws b (wordTarget S (ws.get b))
          rw [hq,thetaBranchPosition_target S ws b]
        · omega
    | succ n ih =>
        intro hn
        obtain ⟨t,ht,hRank,hPrevHigher⟩ := ih (by omega)
        obtain ⟨r,hNext,hRankNext⟩ :=
          thetaCycle_private_continues_down S ws hLong C
            (thetaCycleAdvance C.length_pos q (n + 1))
            b t ht hPrevHigher
        obtain ⟨u,hu⟩ := hArc ((n + 1) + 1)
          (by omega) (by omega)
        have hNextIndex :
            cyclicNext C.length_pos
              (thetaCycleAdvance C.length_pos q (n + 1)) =
            thetaCycleAdvance C.length_pos q ((n + 1) + 1) := rfl
        have hNextPrivate :
            C.vertices (cyclicNext C.length_pos
              (thetaCycleAdvance C.length_pos q (n + 1))) =
              (.inr ⟨b,u⟩ : thetaVertices S ws) := by
          rw [hNextIndex]
          exact hu
        have hPosEq : r = u.val := by
          apply (thetaBranchPosition_injective S ws b)
          exact hNext.symm.trans
            (hNextPrivate.trans
              (thetaBranchPosition_interior S ws b u).symm)
        have hRankU :
            wordPositionRank S (ws.get b) u.val + ((n + 1) + 1) =
              wordPositionRank S (ws.get b)
                (wordTarget S (ws.get b)) := by
          rw [hPosEq] at hRankNext
          omega
        refine ⟨u,hu,hRankU,t.val,?_,?_⟩
        · rw [thetaCycleAdvance_prev_succ C.length_pos q (n + 1)]
          rw [ht, thetaBranchPosition_interior S ws b t]
        · omega
  intro m hm hml
  let n : Nat := m - 1
  have hn : n + 1 = m := by
    dsimp only [n]
    omega
  obtain ⟨t,ht,hRank,_⟩ := hGo n (by omega)
  refine ⟨t,?_,?_⟩
  · simpa only [hn] using ht
  · omega

end CCO.StrongExact
