import CCO.StrongExact.ThetaPrivateIncidence

/-! Any private neighbor of the shared left root has actual word rank one.
This retains all original sorts and genuine diversity labels. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaPrivate_adj_left_rank_one
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (p : wordInterior S (ws.get b))
    (h : thetaAdjacent S ws (.inr ⟨b,p⟩) (thetaLeft S ws)) :
    wordPositionRank S (ws.get b) p.val = 1 := by
  obtain ⟨q, hq, hDirection⟩ :=
    thetaPrivate_neighbor_rank S ws b p (thetaLeft S ws) h
  have hSource : q = wordSource S (ws.get b) := by
    apply (thetaBranchPosition_injective S ws b)
    exact hq.symm.trans (thetaBranchPosition_source S ws b).symm
  have hZero : wordPositionRank S (ws.get b) q = 0 := by
    rw [hSource]
    exact wordSource_rank_zero S (ws.get b)
  rcases hDirection with hUp | hDown
  · omega
  · omega

end CCO.StrongExact
