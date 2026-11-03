import CCO.UnaryTermsReturn.CompletedNamedPrimitives

/-!
# B052 C13–C15: actual named unary words are reachable via true primitives

The complete interpreted real-or-represented-hidden carrier already has
a finite primitive three-way signature: old real-to-quotient projections,
named upward maps, and B049 nonempty identity-free RAW quotient
transitions. Here we construct its reflexive/transitive unary reachability
from those literal source-facing steps.

Every B049 named hidden word, no matter its finite syntax length, is a
path of THESE primitives. Each genuine real-to-hidden term first uses
one actual F_J projection and then the named hidden word. An orphan
quotient generator follows a hidden word directly, without adjoining
a representative real vertex.

Consequently the genuine named-term value sets in the full interpreted
carrier are contained in its actual primitive reachability. The converse
direction, needed for the final equality of closures, is kept separate;
this module never derives a bound merely from finite syntax and never
asserts that arbitrary partial total-unary inputs obey these equations.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- Reflexive finite reachability via ACTUAL named terminal unary
primitive steps, with source/target tagged types intact. -/
inductive OriginalCompletedNamedReachable
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    OriginalCompletedNamedCarrier S H →
      OriginalCompletedNamedCarrier S H → Prop where
  | refl (x : OriginalCompletedNamedCarrier S H) :
      OriginalCompletedNamedReachable H sap nr2 x x
  | step {x y z : OriginalCompletedNamedCarrier S H}
      (h : OriginalCompletedNamedReachable H sap nr2 x y)
      (e : OriginalCompletedNamedStep S H sap nr2 y z) :
      OriginalCompletedNamedReachable H sap nr2 x z

/-- Composition of two actual source-facing primitive paths.
The two paths share precisely the same literal middle vertex. -/
theorem original_completed_named_reachable_trans
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {x y z : OriginalCompletedNamedCarrier S H}
    (hxy : OriginalCompletedNamedReachable S H sap nr2 x y)
    (hyz : OriginalCompletedNamedReachable S H sap nr2 y z) :
    OriginalCompletedNamedReachable S H sap nr2 x z := by
  induction hyz with
  | refl _ => exact hxy
  | step h e ih => exact .step ih e

/-- EVERY B049 genuine named hidden unary term evaluates through
a finite chain of the actual primitive terminal symbols. The
proof is induction on the COMPLETE named grammar, including
identity, upward maps and arbitrary RAW transition sequences. -/
theorem original_completed_named_word_reachable
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι}
    {D : OriginalNamedHiddenCoordinate S H i}
    {E : OriginalNamedHiddenCoordinate S H j}
    (word : OriginalNamedRawUnaryTerm S H sap nr2 D E)
    (q : Quotient D.val.val) :
    OriginalCompletedNamedReachable S H sap nr2
      (originalCompletedNamedHiddenNode S H D q)
      (originalCompletedNamedHiddenNode S H E
        (OriginalNamedRawUnaryTerm.eval S H sap nr2 word q)) := by
  induction word generalizing q with
  | ident D =>
      exact .refl _
  | up word hEF ih =>
      exact .step (ih q)
        (.upward _ _ hEF
          (OriginalNamedRawUnaryTerm.eval S H sap nr2 word q))
  | transition a word ih =>
      exact .step (ih q)
        (.rawTransition a
          (OriginalNamedRawUnaryTerm.eval S H sap nr2 word q))

/-- A genuine real-source named term is a path: first the ACTUAL
projection F_D, then the B049 named hidden word on the literal
quotient class. The target remains its actual represented FULL MI
hidden class; no choice of a section or chart is involved. -/
theorem original_completed_real_term_reachable
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i)
    (d : OriginalRealNamedTermChoice S H sap nr2 i) :
    OriginalCompletedNamedReachable S H sap nr2
      (.inl (⟨i,x⟩ : Sigma X))
      (.inr (originalCompletedRealTermHiddenValue
        S H sap nr2 x d)) := by
  obtain ⟨j,⟨D,⟨E,word⟩⟩⟩ := d
  change OriginalCompletedNamedReachable S H sap nr2
    (.inl (⟨i,x⟩ : Sigma X))
    (originalCompletedNamedHiddenNode S H E
      (OriginalNamedRawUnaryTerm.eval S H sap nr2 word
        (Quotient.mk D.val.val x)))
  have hProjection : OriginalCompletedNamedReachable
      S H sap nr2
      (.inl (⟨i,x⟩ : Sigma X))
      (originalCompletedNamedHiddenNode S H D
        (Quotient.mk D.val.val x)) :=
    .step (.refl _) (.projection D x)
  exact original_completed_named_reachable_trans
    S H sap nr2 hProjection
    (original_completed_named_word_reachable
      S H sap nr2 word (Quotient.mk D.val.val x))

/-- An orphan quotient-generated named term is a path
entirely inside the hidden summand. The old representative
used to establish normal-code finiteness is NOT made a root. -/
theorem original_completed_hidden_term_reachable
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val)
    (d : OriginalHiddenNamedTermChoice S H sap nr2 D) :
    OriginalCompletedNamedReachable S H sap nr2
      (originalCompletedNamedHiddenNode S H D q)
      (.inr (originalCompletedHiddenTermHiddenValue
        S H sap nr2 D q d)) := by
  obtain ⟨j,⟨F,word⟩⟩ := d
  change OriginalCompletedNamedReachable S H sap nr2
    (originalCompletedNamedHiddenNode S H D q)
    (originalCompletedNamedHiddenNode S H F
      (OriginalNamedRawUnaryTerm.eval S H sap nr2 word q))
  exact original_completed_named_word_reachable
    S H sap nr2 word q

/-- No genuine real-generated term VALUE escapes the primitive
closure of its ACTUAL real root. This applies to the entire
represented hidden target carrier, not an overcounting raw-code
supertype or a merely finite unary-function syntax. -/
theorem original_completed_real_values_reachable
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    originalCompletedRealGeneratedValues S H sap nr2 x ⊆
      {v | OriginalCompletedNamedReachable S H sap nr2
        (.inl (⟨i,x⟩ : Sigma X)) v} := by
  intro v hv
  rcases hv with hv | hv
  · have heq := Set.mem_singleton_iff.mp hv
    subst v
    exact .refl _
  · rcases hv with ⟨z, ⟨d,rfl⟩,rfl⟩
    exact original_completed_real_term_reachable S H sap nr2 x d

/-- The analogous complete-carrier inclusion for EVERY orphan
hidden quotient generator, without adding any real roots or
assuming unary-admissibility of unrelated partial inputs. -/
theorem original_completed_hidden_values_reachable
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    originalCompletedHiddenGeneratedValues S H sap nr2 D q ⊆
      {v | OriginalCompletedNamedReachable S H sap nr2
        (originalCompletedNamedHiddenNode S H D q) v} := by
  rintro v ⟨z, ⟨d,rfl⟩,rfl⟩
  exact original_completed_hidden_term_reachable S H sap nr2 D q d

end CCO.UnaryTermsReturn
