import CCO.StrongExact.ThetaPrivateRankReadout

/-!
# C07: finite rank on the hard theta minus its right root

All private word vertices have strictly positive word rank, while the
common left root has rank zero. A branch position other than the
common right root has its original literal word rank. The right root
gets a dummy zero; no theorem will read its rank in that case.

This is source-independent finite combinatorics used to exclude
one-root simple cycles via a maximum-rank argument.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- An interior formal position of a positive word is not its first
position, so its strictly increasing word rank cannot be zero. -/
theorem wordInterior_rank_pos (word : PositiveWord S i j)
    (p : wordInterior S word) :
    0 < wordPositionRank S word p.val := by
  by_contra h
  have hzero : wordPositionRank S word p.val = 0 := by omega
  have hsource : wordPositionRank S word p.val =
      wordPositionRank S word (wordSource S word) := by
    rw [wordSource_rank_zero S word]
    exact hzero
  exact p.property.1 ((wordPositionRank_injective S word) hsource)

/-- Global finite rank on theta formal vertices excluding the right
root, which receives a dummy value. Repeated original sorts are fine. -/
def thetaExceptRightRank (ws : List (PositiveWord S i j)) :
    thetaVertices S ws → Nat
  | .inl _ => 0
  | .inr ⟨b,p⟩ => wordPositionRank S (ws.get b) p.val

theorem thetaExceptRightRank_private_pos
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length) (p : wordInterior S (ws.get b)) :
    0 < thetaExceptRightRank S ws (.inr ⟨b,p⟩) :=
  wordInterior_rank_pos S (ws.get b) p

/-- On any branch position except the RIGHT root, global theta
rank agrees with its original finite line rank. -/
theorem thetaExceptRightRank_of_branch
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length) (q : wordPositions S (ws.get b))
    (hRight : thetaBranchPosition S ws b q ≠ thetaRight S ws) :
    thetaExceptRightRank S ws (thetaBranchPosition S ws b q) =
      wordPositionRank S (ws.get b) q := by
  classical
  by_cases hSource : q = wordSource S (ws.get b)
  · subst q
    rw [thetaBranchPosition_source S ws b, wordSource_rank_zero S (ws.get b)]
    rfl
  · by_cases hTarget : q = wordTarget S (ws.get b)
    · subst q
      exact False.elim (hRight (thetaBranchPosition_target S ws b))
    · let p : wordInterior S (ws.get b) := ⟨q,hSource,hTarget⟩
      change thetaExceptRightRank S ws
          (thetaBranchPosition S ws b p.val) =
        wordPositionRank S (ws.get b) p.val
      rw [thetaBranchPosition_interior S ws b p]
      rfl

end CCO.StrongExact
