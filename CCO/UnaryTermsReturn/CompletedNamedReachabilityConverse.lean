import CCO.UnaryTermsReturn.CompletedNamedStepClosure
import CCO.UnaryTermsReturn.TermComposition

/-!
# B052 C13–C15: reverse actual primitive reachability to named unary words

The previous source-facing modules construct all genuine terminal
primitives on the EXACT represented real/quotient carriers and
prove that every already named B049 term evaluates along a
primitive-step path. This receiver attempts the nontrivial
converse: every such path from an orphan represented quotient
generator has a literal B049 named hidden term as witness.

The induction must preserve the actual proper FULL source and
target kernels at every step. There are no quotient-to-real
symbols or fabricated STRONG identity atoms. The word is
assembled using ONLY the accepted B049 identity, upward and
RAW transition constructors; it is not a postulated section.

This source-facing receiver is WIP until the exact Lean build
confirms dependent source/target pattern matching. No source
instance is to be submitted while unverified.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- Every ACTUAL primitive path from an orphan represented
hidden coordinate is the value of one genuine named B049
unary term on precisely that source quotient class. -/
theorem original_completed_hidden_reachable_has_named_word
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val)
    {v : OriginalCompletedNamedCarrier S H}
    (h : OriginalCompletedNamedReachable S H sap nr2
      (originalCompletedNamedHiddenNode S H D q) v) :
    ∃ (j : ι) (E : OriginalNamedHiddenCoordinate S H j)
      (word : OriginalNamedRawUnaryTerm S H sap nr2 D E),
      v = originalCompletedNamedHiddenNode S H E
        (OriginalNamedRawUnaryTerm.eval S H sap nr2 word q) := by
  induction h with
  | refl =>
      exact ⟨i,D,.ident D,rfl⟩
  | step h e ih =>
      obtain ⟨j,F,word,rfl⟩ := ih
      cases e with
      | projection E x =>
          contradiction
      | upward E K hEK q' =>
          exact ⟨_,K,.up word hEK,rfl⟩
      | rawTransition a q' =>
          exact ⟨_,
            originalNamedRawTransitionSymbol_target S H sap nr2 a,
            .transition a word,rfl⟩

end CCO.UnaryTermsReturn
