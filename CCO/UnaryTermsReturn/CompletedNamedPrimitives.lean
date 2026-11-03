import CCO.UnaryTermsReturn.CompletedNamedCarrier
import CCO.UnaryTermsReturn.TermComposition

/-!
# B052 D01/D04/D08: actual finite named terminal unary primitives

The primitive unary signature here has precisely the three genuine
classes of old-source names: real-to-represented-proper-quotient
projections, upward maps between represented proper coordinates,
and original B049 identity-free nonempty invariant RAW quotient
transitions. The source and target old sorts, full equivalence
kernels and actual quotient maps are all retained.

There is a FINITE type of primitive symbols because the original
sorts, represented FULL MI kernels, and nonempty invariant old
orbital relations are finite. The associated typed graph is
given over the exact completed real-or-represented-hidden carrier.
It is a graph of genuinely named operations, NOT an arbitrary
total-unary partial input or a fabricated quotient-to-real map.

The existing B049 grammar is the composable term closure of
these constructors, including its existing identities. Root
equations and finite many-sorted completed-age consumers are
independent; no hidden SAP or HN theorem is inserted.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- Genuine finite menu of real-to-hidden old quotient
projection symbols. A different represented full original
kernel is a different existing hidden target sort. -/
abbrev OriginalCompletedProjectionSymbol
    (H : HomogeneousSource S G) :=
  Σ i : ι, OriginalNamedHiddenCoordinate S H i

/-- Genuine finite menu of source-coordinate upward maps:
the source and target are represented proper full kernels on
the SAME original real sort, and the actual order is retained. -/
abbrev OriginalCompletedUpwardSymbol
    (H : HomogeneousSource S G) :=
  Σ i : ι,
    {p : OriginalNamedHiddenCoordinate S H i ×
      OriginalNamedHiddenCoordinate S H i //
      p.1.val ≤ p.2.val}

/-- Every genuine named old RAW quotient transport symbol,
including all allowed many-atom invariant identity-free
relations (not merely atomic branches), with exact old sorts. -/
abbrev OriginalCompletedRawSymbol
    (H : HomogeneousSource S G) :=
  Σ i : ι, Σ j : ι, OriginalNamedRawTransitionSymbol S H i j

/-- The actual terminal three-way primitive unary menu.
The identity is the existing EMPTY term, not a new
positive STRONG diagonal atom or an extra transition. -/
abbrev OriginalCompletedPrimitiveSymbol
    (H : HomogeneousSource S G) :=
  OriginalCompletedProjectionSymbol S H ⊕
    (OriginalCompletedUpwardSymbol S H ⊕
      OriginalCompletedRawSymbol S H)

/-- The actual primitive named unary language is FINITE:
no bound on the length or number of composable terms is
claimed, and no finite real/quotient carriers are assumed. -/
theorem original_completed_primitive_symbols_finite
    (H : HomogeneousSource S G) :
    Finite (OriginalCompletedPrimitiveSymbol S H) := by
  letI : Fintype ι := S.finiteSort
  haveI (i : ι) :
      Finite (OriginalNamedHiddenCoordinate S H i) :=
    original_named_hidden_coordinates_finite S H
  haveI (i : ι) :
      Finite {p : OriginalNamedHiddenCoordinate S H i ×
          OriginalNamedHiddenCoordinate S H i //
          p.1.val ≤ p.2.val} :=
    Finite.of_injective Subtype.val Subtype.val_injective
  haveI (i j : ι) :
      Finite (OriginalNamedRawTransitionSymbol S H i j) :=
    originalNamedRawTransitionSymbol_finite S H
  infer_instance

/-- A directed edge of ONE ACTUAL well-typed named primitive.
The graph's vertices are complete old real and represented
proper-full-quotient tagged values. Mixed original sorts,
diagonal real identity, and exact quotient classes are retained.
No edge returns a hidden quotient vertex to a real point. -/
inductive OriginalCompletedNamedStep
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S) :
    OriginalCompletedNamedCarrier S H →
      OriginalCompletedNamedCarrier S H → Prop where
  | projection {i : ι}
      (D : OriginalNamedHiddenCoordinate S H i)
      (x : X i) :
      OriginalCompletedNamedStep H sap nr2
        (.inl (⟨i,x⟩ : Sigma X))
        (originalCompletedNamedHiddenNode S H D
          (Quotient.mk D.val.val x))
  | upward {i : ι}
      (D E : OriginalNamedHiddenCoordinate S H i)
      (hDE : D.val ≤ E.val)
      (q : Quotient D.val.val) :
      OriginalCompletedNamedStep H sap nr2
        (originalCompletedNamedHiddenNode S H D q)
        (originalCompletedNamedHiddenNode S H E
          (Quot.mapRight hDE q))
  | rawTransition {i j : ι}
      (a : OriginalNamedRawTransitionSymbol S H i j)
      (q : Quotient a.val.1.val.val) :
      OriginalCompletedNamedStep H sap nr2
        (originalCompletedNamedHiddenNode S H a.val.1 q)
        (originalCompletedNamedHiddenNode S H
          (originalNamedRawTransitionSymbol_target
            S H sap nr2 a)
          (originalNamedRawTransitionSymbol_function
            S H sap nr2 a q))

/-- An ACTUAL source10 unary primitive cannot send any
represented hidden quotient value back into the real
summand. This is a typed statement about all three real
source terminal names, not a syntactic restriction on
unrelated total-unary partial structures. -/
theorem original_completed_named_step_no_hidden_to_real
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    (v : OriginalCompletedNamedHiddenValue S H)
    (x : Sigma X) :
    ¬ OriginalCompletedNamedStep S H sap nr2
      (.inr v) (.inl x) := by
  intro h
  cases h

/-- The genuine upward primitive is exactly the old named
B049 unary word formed by its existing identity and upward
constructor; there is no separate new quotient function. -/
theorem original_completed_upward_is_named_word
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D E : OriginalNamedHiddenCoordinate S H i)
    (hDE : D.val ≤ E.val) (q : Quotient D.val.val) :
    OriginalNamedRawUnaryTerm.eval S H sap nr2
      (originalNamedUpTerm S H sap nr2 D E hDE) q =
      Quot.mapRight hDE q :=
  originalNamedUpTerm_eval S H sap nr2 D E hDE q

/-- A primitive original RAW transition likewise evaluates
as the existing genuine named one-letter B049 word, with
its actual transported represented target, not an assumed
abstract quotient chart. -/
theorem original_completed_raw_is_named_word
    (H : HomogeneousSource S G)
    (sap : AgeSAP S) (nr2 : Selectors.OriginalNR2 S)
    {i j : ι} (a : OriginalNamedRawTransitionSymbol S H i j)
    (q : Quotient a.val.1.val.val) :
    OriginalNamedRawUnaryTerm.eval S H sap nr2
      (OriginalNamedRawUnaryTerm.transition a
        (OriginalNamedRawUnaryTerm.ident a.val.1)) q =
      originalNamedRawTransitionSymbol_function
        S H sap nr2 a q := rfl

end CCO.UnaryTermsReturn
