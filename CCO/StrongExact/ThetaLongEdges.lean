import CCO.StrongExact.ThetaLineRank
import CCO.StrongExact.ThetaInteriors

/-!
# C07: long positive private paths have no direct root-to-root edge

Every positive word has distinct formal endpoints and an injective
rank map. The first root has rank zero; the last root has strictly
positive rank. Prepending a new genuine diversity letter increases
the last root's rank by one. Consequently every word with at least
two letters has its last root at rank >= 2.

Since each genuine word edge increases rank by exactly one, no such
long private branch can contain a literal direct root-to-root edge.
This is the algebraic separator that allows merging duplicate
single-letter branches BEFORE building the simple theta diagram.
It is a statement about FINITE FORMAL POSITIONS, not source orbitals,
and uses no SAP, CCO, RAW identity or new assumption.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j k : ι}

/-- Any genuine positive word ends at rank at least one,
even when its typed endpoint sorts coincide. -/
theorem wordTarget_rank_positive (word : PositiveWord S i j) :
    0 < wordPositionRank S word (wordTarget S word) := by
  have hne := wordSource_ne_target S word
  have hinj := wordPositionRank_injective S word
  have hnonzero :
      wordPositionRank S word (wordTarget S word) ≠ 0 := by
    intro hzero
    apply hne
    apply hinj
    rw [wordSource_rank_zero S word]
    exact hzero.symm
  omega

/-- A positive word with a nonempty tail of length at least one
has last formal vertex at rank two or higher. -/
theorem wordTarget_rank_cons_ge_two
    (a : S.Atom i j) (tail : PositiveWord S j k) :
    2 ≤ wordPositionRank S (.cons a tail)
      (wordTarget S (.cons a tail)) := by
  change 2 ≤ 1 + wordPositionRank S tail (wordTarget S tail)
  have hTail := wordTarget_rank_positive S tail
  omega

/-- No letter of a positive word of length at least two goes directly
from its global source to its global target. This excludes spurious
parallel root edges in the hard theta graph. -/
theorem no_direct_letter_in_long_word
    (a : S.Atom i j) (tail : PositiveWord S j k)
    (e : wordEdgeIndex S (.cons a tail)) :
    ¬ (wordEdgeSource S (.cons a tail) e =
         wordSource S (.cons a tail) ∧
       wordEdgeTarget S (.cons a tail) e =
         wordTarget S (.cons a tail)) := by
  rintro ⟨hs, ht⟩
  have heq := wordEdge_rank_step S (.cons a tail) e
  rw [hs, ht, wordSource_rank_zero S (.cons a tail)] at heq
  have hBig := wordTarget_rank_cons_ge_two S a tail
  omega

end CCO.StrongExact
