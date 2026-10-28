import CCO.StrongExact.ThetaExceptRightRank

/-!
# C07: dual finite rank away from the LEFT theta root

For each word position, count the old positive letters still needed
to reach the right endpoint. Its value is positive at private
vertices, zero at the common right root, and faithfully reads the
rank of every branch position other than the left root.

This is finite formal graph combinatorics: equality and repeated
named sorts are not promoted to diversity letters.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- The target of a positive word has maximal finite line rank. -/
theorem wordPositionRank_le_target
    (word : PositiveWord S i j)
    (p : wordPositions S word) :
    wordPositionRank S word p ≤
      wordPositionRank S word (wordTarget S word) := by
  induction word with
  | single a =>
      cases p <;> simp [wordPositionRank, wordTarget]
  | cons a tail ih =>
      cases p with
      | none =>
          change 0 ≤ 1 + wordPositionRank S tail (wordTarget S tail)
          omega
      | some q =>
          change 1 + wordPositionRank S tail q ≤
            1 + wordPositionRank S tail (wordTarget S tail)
          exact Nat.add_le_add_left (ih q) 1

/-- The remaining distance to the target is positive at every
strictly interior position, even when endpoint sorts agree. -/
theorem wordInterior_remaining_pos
    (word : PositiveWord S i j)
    (p : wordInterior S word) :
    0 < wordPositionRank S word (wordTarget S word) -
      wordPositionRank S word p.val := by
  have hBound := wordPositionRank_le_target S word p.val
  have hNe : wordPositionRank S word p.val ≠
      wordPositionRank S word (wordTarget S word) := by
    intro h
    exact p.property.2 ((wordPositionRank_injective S word) h)
  omega

/-- Global rank on the theta graph without its left root.
Both formal roots are assigned zero; the left-root case will
always be excluded before the rank is read as a branch rank. -/
def thetaExceptLeftRank (ws : List (PositiveWord S i j)) :
    thetaVertices S ws → Nat
  | .inl _ => 0
  | .inr ⟨b,p⟩ =>
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
        wordPositionRank S (ws.get b) p.val

theorem thetaExceptLeftRank_private_pos
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length) (p : wordInterior S (ws.get b)) :
    0 < thetaExceptLeftRank S ws (.inr ⟨b,p⟩) :=
  wordInterior_remaining_pos S (ws.get b) p

/-- The dual theta rank reads the true distance to the right
endpoint at every embedded branch position except the left root. -/
theorem thetaExceptLeftRank_of_branch
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length) (q : wordPositions S (ws.get b))
    (hLeft : thetaBranchPosition S ws b q ≠ thetaLeft S ws) :
    thetaExceptLeftRank S ws (thetaBranchPosition S ws b q) =
      wordPositionRank S (ws.get b) (wordTarget S (ws.get b)) -
        wordPositionRank S (ws.get b) q := by
  classical
  by_cases hTarget : q = wordTarget S (ws.get b)
  · subst q
    rw [thetaBranchPosition_target S ws b]
    simp [thetaExceptLeftRank, thetaRight]
  · by_cases hSource : q = wordSource S (ws.get b)
    · subst q
      exact False.elim (hLeft (thetaBranchPosition_source S ws b))
    · let p : wordInterior S (ws.get b) :=
        ⟨q, hSource, hTarget⟩
      change thetaExceptLeftRank S ws
          (thetaBranchPosition S ws b p.val) = _
      rw [thetaBranchPosition_interior S ws b p]
      rfl

end CCO.StrongExact
