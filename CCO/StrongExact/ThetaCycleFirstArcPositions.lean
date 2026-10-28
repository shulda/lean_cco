import CCO.StrongExact.ThetaCycleFirstArcLength
import CCO.StrongExact.ThetaExceptLeftRank

/-!
# C07: the first root arc contains EVERY formal word position

Once the old right root has been reached at exactly the target
rank, the proved strict interior rank correspondence identifies
each original word position with a unique cyclic position.
No edge/letter constraints are invented: this is an equality
between actual tagged theta vertices.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaCycle_left_arc_all_positions
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
          (.inr ⟨b,t⟩ : thetaVertices S ws))
    (z : wordPositions S (ws.get b)) :
    C.vertices (thetaCycleAdvance C.length_pos p
      (wordPositionRank S (ws.get b) z)) =
      thetaBranchPosition S ws b z := by
  have hFull := thetaCycle_left_arc_target_rank S ws hLong C
    p q k hp hq hk hReached b hArc
  let m := wordPositionRank S (ws.get b) z
  have hBound : m ≤ k := by
    change wordPositionRank S (ws.get b) z ≤ k
    rw [← hFull]
    exact wordPositionRank_le_target S (ws.get b) z
  by_cases hmZero : m = 0
  · have hzZero : wordPositionRank S (ws.get b) z = 0 := hmZero
    have hRankEq :
        wordPositionRank S (ws.get b) z =
        wordPositionRank S (ws.get b)
          (wordSource S (ws.get b)) := by
      rw [wordSource_rank_zero S (ws.get b)]
      exact hzZero
    have hz : z = wordSource S (ws.get b) :=
      (wordPositionRank_injective S (ws.get b)) hRankEq
    subst z
    rw [wordSource_rank_zero S (ws.get b)]
    change C.vertices p =
      thetaBranchPosition S ws b (wordSource S (ws.get b))
    rw [hp, thetaBranchPosition_source S ws b]
  · by_cases hmEnd : m = k
    · have hRankEq :
          wordPositionRank S (ws.get b) z =
          wordPositionRank S (ws.get b)
            (wordTarget S (ws.get b)) := by
        rw [hFull]
        exact hmEnd
      have hz : z = wordTarget S (ws.get b) :=
        (wordPositionRank_injective S (ws.get b)) hRankEq
      subst z
      rw [hFull, hReached]
      exact hq.trans (thetaBranchPosition_target S ws b).symm
    · have hmPos : 0 < m := by omega
      have hmLt : m < k := by omega
      obtain ⟨t,ht,hRank⟩ :=
        thetaCycle_left_arc_rank_matches_distance S ws hLong C
          p q k hp hq hk hReached b hArc m hmPos hmLt
      have hzEq : z = t.val := by
        apply (wordPositionRank_injective S (ws.get b))
        change wordPositionRank S (ws.get b) z =
          wordPositionRank S (ws.get b) t.val
        rw [hRank]
      subst z
      rw [hRank]
      exact ht.trans (thetaBranchPosition_interior S ws b t).symm

end CCO.StrongExact
