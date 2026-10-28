import CCO.StrongExact.ThetaLineRank
import CCO.StrongExact.ThetaBranchInjective

/-!
# C07: uniqueness and orientation of private positive-word letters

The ranked formal word line is a genuine directed path, not just a
walk. A target vertex has at most one incoming word letter, and two
letters of the same line cannot form an oppositely oriented two-cycle.

These facts follow from strictly increasing integer rank and the
already-proved injection of the word edge-source map. There is no
semantic source assumption here.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- A literal positive-word edge cannot end at the first formal
vertex of that word. -/
theorem wordEdgeTarget_ne_first
    (word : PositiveWord S i j) (e : wordEdgeIndex S word) :
    wordEdgeTarget S word e ≠ wordSource S word := by
  intro heq
  have hStep := wordEdge_rank_step S word e
  rw [heq, wordSource_rank_zero S word] at hStep
  omega

/-- One incoming diversity letter per formal word vertex. -/
theorem wordEdgeTarget_injective
    (word : PositiveWord S i j) :
    Function.Injective (wordEdgeTarget S word) := by
  intro e f hSame
  have hStepE := wordEdge_rank_step S word e
  have hStepF := wordEdge_rank_step S word f
  have hSameRank :
      wordPositionRank S word (wordEdgeSource S word e) =
        wordPositionRank S word (wordEdgeSource S word f) := by
    rw [hSame] at hStepE
    omega
  exact (wordEdgeSource_injective S word)
    ((wordPositionRank_injective S word) hSameRank)

/-- Two distinct or equal private word letters cannot reverse one
another as ordered pairs of formal endpoints. Their rank increments
would add to an impossible positive two-cycle. -/
theorem wordEdge_no_reversed_pair
    (word : PositiveWord S i j)
    (e f : wordEdgeIndex S word) :
    ¬ (wordEdgeSource S word e = wordEdgeTarget S word f ∧
       wordEdgeTarget S word e = wordEdgeSource S word f) := by
  rintro ⟨hSrc,hDst⟩
  have hStepE := wordEdge_rank_step S word e
  have hStepF := wordEdge_rank_step S word f
  rw [hSrc,hDst] at hStepE
  omega

/-- The globally shared-root embedding of a private word line
preserves one-outgoing-edge uniqueness. -/
theorem thetaBranchEdgeSource_injective
    (ws : List (PositiveWord S i j)) (b : Fin ws.length) :
    Function.Injective (thetaBranchEdgeSource S ws b) := by
  intro e f hSame
  apply (wordEdgeSource_injective S (ws.get b))
  apply (thetaBranchPosition_injective S ws b)
  exact hSame

/-- Similarly, at most one incoming edge has a given terminal theta
vertex inside a fixed private branch. -/
theorem thetaBranchEdgeTarget_injective
    (ws : List (PositiveWord S i j)) (b : Fin ws.length) :
    Function.Injective (thetaBranchEdgeTarget S ws b) := by
  intro e f hSame
  apply (wordEdgeTarget_injective S (ws.get b))
  apply (thetaBranchPosition_injective S ws b)
  exact hSame

/-- No directed letter pair in one private theta branch can be the
reverse of another; this rules out hidden formal two-cycles even
when the literal endpoint named sorts are identical. -/
theorem thetaBranchEdge_no_reversed_pair
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (e f : wordEdgeIndex S (ws.get b)) :
    ¬ (thetaBranchEdgeSource S ws b e =
         thetaBranchEdgeTarget S ws b f ∧
       thetaBranchEdgeTarget S ws b e =
         thetaBranchEdgeSource S ws b f) := by
  rintro ⟨hSrc,hDst⟩
  apply wordEdge_no_reversed_pair S (ws.get b) e f
  constructor
  · apply (thetaBranchPosition_injective S ws b)
    exact hSrc
  · apply (thetaBranchPosition_injective S ws b)
    exact hDst

end CCO.StrongExact
