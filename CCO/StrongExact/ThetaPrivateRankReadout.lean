import CCO.StrongExact.ThetaPrivateIncidence

/-!
# C07: rank readout of a theta position known to be private

A point on a word branch is equal to a private original-vertex tag
only when its branch index and actual finite rank are the corresponding
ones. This small dependent-type bridge is needed to transfer the
local two-sided cycle argument to a global minimum-rank contradiction.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

theorem thetaBranchPosition_eq_private_rank
    (ws : List (PositiveWord S i j))
    (b c : Fin ws.length)
    (q : wordPositions S (ws.get b))
    (p : wordInterior S (ws.get c))
    (he : thetaBranchPosition S ws b q =
      (.inr ⟨c,p⟩ : thetaVertices S ws)) :
    b = c ∧ wordPositionRank S (ws.get b) q =
      wordPositionRank S (ws.get c) p.val := by
  have hpos : thetaBranchPosition S ws c p.val =
      thetaBranchPosition S ws b q := by
    rw [thetaBranchPosition_interior S ws c p]
    exact he.symm
  have hcb : c = b :=
    private_embedded_position_same_branch S ws c b p q hpos
  subst c
  have hq : q = p.val :=
    (thetaBranchPosition_injective S ws b)
      (he.trans (thetaBranchPosition_interior S ws b p).symm)
  subst q
  exact ⟨rfl,rfl⟩

end CCO.StrongExact
