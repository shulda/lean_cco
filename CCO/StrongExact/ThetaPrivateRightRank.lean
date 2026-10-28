import CCO.StrongExact.ThetaPrivateLeftRank
import CCO.StrongExact.ThetaExceptLeftRank

/-! Private neighbors of the RIGHT theta root occupy the penultimate
original word position. This is a literal rank fact, no source axiom. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaPrivate_adj_right_rank_pred
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (p : wordInterior S (ws.get b))
    (h : thetaAdjacent S ws (.inr ⟨b,p⟩) (thetaRight S ws)) :
    wordPositionRank S (ws.get b) p.val + 1 =
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) := by
  obtain ⟨q, hq, hDirection⟩ :=
    thetaPrivate_neighbor_rank S ws b p (thetaRight S ws) h
  have hTarget : q = wordTarget S (ws.get b) := by
    apply (thetaBranchPosition_injective S ws b)
    exact hq.symm.trans (thetaBranchPosition_target S ws b).symm
  have hBound := wordPositionRank_le_target S (ws.get b) p.val
  rcases hDirection with hForward | hBackward
  · simpa only [hTarget] using hForward.symm
  · rw [hTarget] at hBackward
    omega

end CCO.StrongExact
