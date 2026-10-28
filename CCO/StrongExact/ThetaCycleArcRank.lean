import CCO.StrongExact.ThetaCycleFirstArc
import CCO.StrongExact.ThetaCycleAdvancePrev
import CCO.StrongExact.ThetaCycleOrientation
import CCO.StrongExact.ThetaPrivateLeftRank

/-!
# C07: rank of every vertex on the left-to-right private theta arc

A simple theta cycle starts at the left root at word rank zero.
The first private point of its forward arc has rank one.
At each subsequent private point, the proved two-sided local cycle
orientation forces the next rank to increase by exactly one.
Consequently the position reached after m cyclic successor steps
has literal original word-position rank m, for all 0<m<k, where k
is the forward distance to the right root.

The result preserves actual named-sort tags and old diversity atoms.
It is not yet a proof of C07 cycle compatibility or 2-Helly.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_left_arc_rank_matches_distance
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
    ∀ m : Nat, 0 < m → m < k →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos p m) =
          (.inr ⟨b,t⟩ : thetaVertices S ws) ∧
        wordPositionRank S (ws.get b) t.val = m := by
  have hGo : ∀ n : Nat, n + 1 < k →
      ∃ t : wordInterior S (ws.get b),
        C.vertices (thetaCycleAdvance C.length_pos p (n + 1)) =
          (.inr ⟨b,t⟩ : thetaVertices S ws) ∧
        wordPositionRank S (ws.get b) t.val = n + 1 ∧
        (∃ r : wordPositions S (ws.get b),
          C.vertices (cyclicPrev C.length_pos
            (thetaCycleAdvance C.length_pos p (n + 1))) =
              thetaBranchPosition S ws b r ∧
          wordPositionRank S (ws.get b) r + 1 =
            wordPositionRank S (ws.get b) t.val) := by
    intro n
    induction n with
    | zero =>
        intro hn
        obtain ⟨t,ht⟩ := hArc 1 (by omega) (by omega)
        have htNext : C.vertices (cyclicNext C.length_pos p) =
            (.inr ⟨b,t⟩ : thetaVertices S ws) := by
          simpa only [thetaCycleAdvance] using ht
        have hAdj : thetaAdjacent S ws
            (.inr ⟨b,t⟩ : thetaVertices S ws)
            (thetaLeft S ws) := by
          have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
            (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
            (C.next_ne p)).mp (C.specified p)
          apply thetaAdjacent_symmetric S ws
          rw [hp,htNext] at he
          exact he
        have hRank := thetaPrivate_adj_left_rank_one S ws b t hAdj
        refine ⟨t,ht,hRank,wordSource S (ws.get b),?_,?_⟩
        · rw [thetaCycleAdvance_prev_succ C.length_pos p 0]
          change C.vertices p =
            thetaBranchPosition S ws b (wordSource S (ws.get b))
          rw [hp,thetaBranchPosition_source S ws b]
        · rw [wordSource_rank_zero S (ws.get b)]
          omega
    | succ n ih =>
        intro hn
        obtain ⟨t,ht,hRank,hPrevLower⟩ := ih (by omega)
        obtain ⟨r,hNext,hRankNext⟩ :=
          thetaCycle_private_continues_up S ws hLong C
            (thetaCycleAdvance C.length_pos p (n + 1))
            b t ht hPrevLower
        obtain ⟨u,hu⟩ := hArc ((n + 1) + 1)
          (by omega) (by omega)
        have hNextIndex :
            cyclicNext C.length_pos
              (thetaCycleAdvance C.length_pos p (n + 1)) =
            thetaCycleAdvance C.length_pos p ((n + 1) + 1) := rfl
        have hPosEq : r = u.val := by
          apply (thetaBranchPosition_injective S ws b)
          calc
            thetaBranchPosition S ws b r =
                C.vertices (cyclicNext C.length_pos
                  (thetaCycleAdvance C.length_pos p (n + 1))) :=
                    hNext.symm
            _ = C.vertices
                (thetaCycleAdvance C.length_pos p ((n + 1) + 1)) := by
                  rw [hNextIndex]
            _ = (.inr ⟨b,u⟩ : thetaVertices S ws) := hu
            _ = thetaBranchPosition S ws b u.val :=
              (thetaBranchPosition_interior S ws b u).symm
        have hRankU :
            wordPositionRank S (ws.get b) u.val = (n + 1) + 1 := by
          rw [hPosEq] at hRankNext
          omega
        refine ⟨u,hu,hRankU,t.val,?_,?_⟩
        · rw [thetaCycleAdvance_prev_succ C.length_pos p (n + 1)]
          rw [ht, thetaBranchPosition_interior S ws b t]
        · omega
  intro m hm hmk
  let n : Nat := m - 1
  have hn : n + 1 = m := by
    dsimp only [n]
    omega
  obtain ⟨t,ht,hRank,_⟩ := hGo n (by omega)
  refine ⟨t,?_,?_⟩
  · simpa only [hn] using ht
  · omega

end CCO.StrongExact
