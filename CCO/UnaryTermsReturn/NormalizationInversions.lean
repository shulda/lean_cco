import CCO.TransitionClosure.OriginalTransportUpwardRewrite
import Lean.Elab.Tactic.Omega

/-!
# B052 D03/C07: exact inversion measure for original unary term normalisation

B049 already proves the REAL semantic upward/transition interchange
and the full normal-form theorem by structural induction on the actual
original typed term syntax. This file separately formalises the numeric
termination argument in source10: in source-to-value operation order,
a "transition before a later upward map" contributes ONE inversion.

The adjacent transition/upward rewrite moves the upward operation
towards the source and reduces the inversion count by exactly one,
including inside arbitrary finite prefixes and suffixes. Semantic
soundness is supplied by the imported B049 literal quotient action,
not postulated here from a formal word rewrite. We count no syntax
identities, and do not infer finiteness of the set of arbitrary words.
-/

namespace CCO.UnaryTermsReturn

/-- A letter in a source-to-value original unary term AFTER removing
existing identity operations and the possible initial real projection.
The actual typed interpretation belongs to B049's genuine quotient
language; this small alphabet only records operation KINDS. -/
inductive OriginalUnaryNormalizationOp where
  | upward
  | transition
  deriving DecidableEq, Repr

/-- Number of upward maps occurring in a finite suffix. -/
def originalUnaryUpwardCount : List OriginalUnaryNormalizationOp → Nat
  | [] => 0
  | .upward :: rest => originalUnaryUpwardCount rest + 1
  | .transition :: rest => originalUnaryUpwardCount rest

/-- D03: one unit for each transition and subsequent upward map,
not for an upward map occurring earlier in the source-to-value word. -/
def originalUnaryTransitionUpwardInversions :
    List OriginalUnaryNormalizationOp → Nat
  | [] => 0
  | .upward :: rest => originalUnaryTransitionUpwardInversions rest
  | .transition :: rest =>
      originalUnaryUpwardCount rest +
        originalUnaryTransitionUpwardInversions rest

/-- Swapping adjacent transition/upward symbols preserves the total
number of upward maps in ANY surrounding prefix and suffix. -/
theorem original_unary_upward_count_swap
    (initialOps suffix : List OriginalUnaryNormalizationOp) :
    originalUnaryUpwardCount
        (initialOps ++ .transition :: .upward :: suffix) =
      originalUnaryUpwardCount
        (initialOps ++ .upward :: .transition :: suffix) := by
  induction initialOps with
  | nil => rfl
  | cons head initialOps ih =>
      cases head with
      | upward =>
          simp only [List.cons_append, originalUnaryUpwardCount]
          rw [ih]
      | transition =>
          simpa only [List.cons_append, originalUnaryUpwardCount] using ih

/-- The source10 adjacent upward interchange decreases D03's
nonnegative potential EXACTLY by one. B049 supplies independently
the equality of the two genuine typed quotient functions. -/
theorem original_unary_transition_upward_inversions_swap
    (initialOps suffix : List OriginalUnaryNormalizationOp) :
    originalUnaryTransitionUpwardInversions
        (initialOps ++ .transition :: .upward :: suffix) =
      originalUnaryTransitionUpwardInversions
        (initialOps ++ .upward :: .transition :: suffix) + 1 := by
  induction initialOps with
  | nil =>
      simp [originalUnaryTransitionUpwardInversions,
        originalUnaryUpwardCount, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm]
  | cons head initialOps ih =>
      cases head with
      | upward =>
          simpa only [List.cons_append,
            originalUnaryTransitionUpwardInversions] using ih
      | transition =>
          simp only [List.cons_append,
            originalUnaryTransitionUpwardInversions]
          rw [original_unary_upward_count_swap initialOps suffix, ih]
          omega

/-- Source10 C07 strict descent for every adjacent inversion
rewrite, with arbitrary context and with unchanged old type order
recorded separately by the accepted B049 interchange theorem. -/
theorem original_unary_transition_upward_swap_decreases
    (initialOps suffix : List OriginalUnaryNormalizationOp) :
    originalUnaryTransitionUpwardInversions
        (initialOps ++ .upward :: .transition :: suffix) <
      originalUnaryTransitionUpwardInversions
        (initialOps ++ .transition :: .upward :: suffix) := by
  rw [original_unary_transition_upward_inversions_swap]
  omega

/-- One allowed local normalization step. Its contextual operation
word is only a LENGTH/KIND abstraction; legality and semantic
quotient types remain those of the genuine accepted B049 term. -/
inductive OriginalUnaryNormalizationSwap :
    List OriginalUnaryNormalizationOp →
    List OriginalUnaryNormalizationOp → Prop where
  | adjacent (initialOps suffix : List OriginalUnaryNormalizationOp) :
      OriginalUnaryNormalizationSwap
        (initialOps ++ .transition :: .upward :: suffix)
        (initialOps ++ .upward :: .transition :: suffix)

/-- Every local swap descends a natural-number measure; hence there
cannot be infinitely many adjacent swaps in a genuine finite term.
The full semantic normalization is B049's structural theorem. -/
theorem original_unary_normalization_swap_strict
    {oldWord newWord : List OriginalUnaryNormalizationOp}
    (h : OriginalUnaryNormalizationSwap oldWord newWord) :
    originalUnaryTransitionUpwardInversions newWord <
      originalUnaryTransitionUpwardInversions oldWord := by
  cases h with
  | adjacent initialOps suffix =>
      exact original_unary_transition_upward_swap_decreases initialOps suffix

end CCO.UnaryTermsReturn
