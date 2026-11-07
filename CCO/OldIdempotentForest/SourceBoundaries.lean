import CCO.GuardedTwoRoot.TypedPrefixStates

/-! Equal idempotent profiles do not identify original atomic words.
The literal word data remain necessary for the specified cycle. -/

universe u v w r
namespace CCO.OldIdempotentForest
open CCO.GuardedTwoRoot
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (sap : AgeSAP S)

include H sap
/-- Even an actual gap's positive word and its literal double have the
same strong value but DIFFERENT original atomic word data. -/
theorem same_idempotent_profile_different_original_words {i : ι}
    (word : PositiveWord S i i)
    (idem : S.product (PositiveWord.profile S word) (PositiveWord.profile S word) =
      PositiveWord.profile S word) :
    PositiveWord.profile S (PositiveWord.append S word word) = PositiveWord.profile S word ∧
      PositiveWord.append S word word ≠ word := by
  constructor
  · exact (PositiveWord.profile_append_of_SAP S H sap word word).trans idem
  · intro he
    have hl := congrArg (TypedPrefix.length S) he
    rw [TypedPrefix.length_append] at hl
    have hp := TypedPrefix.length_pos S word
    omega

end CCO.OldIdempotentForest
