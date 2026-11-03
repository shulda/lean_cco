import CCO.UnaryTermsReturn.ActualGeneratedClosures
import Mathlib.Data.Set.Card

/-!
# B052 C13–C15: entire actual real/represented-hidden carrier

The previous m_typ bound counted correctly tagged original full RAW
normal-code values. Here a hidden vertex is precisely an ACTUAL
original named proper FULL MI quotient value, with proof of
representedness. This is a SUBTYPE of the earlier full tagged
quotient-value carrier, not a choice of extra roots or quotient
representatives. Original old real vertices remain a disjoint summand.

Every genuinely named original real/hidden term evaluates into this
complete interpreted carrier. Forgetting only its proof of named
membership is INJECTIVE; it maps the one-generator value sets
exactly into the existing uniform normal-code-bound sets. Therefore
the same m_typ bounds one-generator values in the true represented
real/hidden carrier, including orphan quotient-only generators.

The generic closed-induced-member and full unary-admissible
isomorphism transport live in GeneratedClosureWords and
FullAdmissibleTransfer. The final consumer must still identify
the whole terminal hidden signature's primitive symbols with the
original B049 named grammar; that identification is NOT silently
assumed or provided by a new external HN theorem here.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- A genuine represented FULL original quotient class:
its original sort, actual full kernel and actual class are
retained as literal data. The proof of named membership is
not an additional hidden coordinate or quotient chart. -/
abbrev OriginalCompletedNamedHiddenValue
    (H : HomogeneousSource S G) :=
  {v : OriginalNormalCodeTargetValue S //
    ∃ D : OriginalNamedHiddenCoordinate S H v.1,
      D.val = v.2.1}

/-- Entire actual interpreted terminal *carrier* before
restricting to a finite completed unary-closed member:
all old real points, disjoint from all actual represented
original hidden quotient-class vertices. -/
abbrev OriginalCompletedNamedCarrier
    (H : HomogeneousSource S G) :=
  (Sigma X) ⊕ OriginalCompletedNamedHiddenValue S H


/-- Embed ONE genuinely named original hidden coordinate class
into the complete real-or-represented-quotient carrier. This
is an actual class, not a choice of a representative or a new
independent quotient chart. -/
def originalCompletedNamedHiddenNode
    (H : HomogeneousSource S G)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    OriginalCompletedNamedCarrier S H :=
  Sum.inr ⟨⟨i,⟨D.val,q⟩⟩,⟨D,rfl⟩⟩

/-- Forget only representedness evidence. This does not
forget the real-sort, full original quotient kernel,
or actual quotient-class value. -/
def originalCompletedCarrierForget
    (H : HomogeneousSource S G) :
    OriginalCompletedNamedCarrier S H →
      (Sigma X) ⊕ OriginalNormalCodeTargetValue S
  | .inl x => .inl x
  | .inr v => .inr v.val

/-- The forgetting map is injective: proof irrelevance
identifies hidden vertices whose actual quotient class,
represented full equivalence and original sort coincide. -/
theorem originalCompletedCarrierForget_injective
    (H : HomogeneousSource S G) :
    Function.Injective (originalCompletedCarrierForget S H) := by
  intro a b h
  cases a with
  | inl x =>
      cases b with
      | inl y =>
          exact congrArg Sum.inl (Sum.inl.inj h)
      | inr y =>
          cases h
  | inr x =>
      cases b with
      | inl y =>
          cases h
      | inr y =>
          exact congrArg Sum.inr
            (Subtype.ext (Sum.inr.inj h))

/-- An actual real-source term has an ACTUAL named full MI
target coordinate. No extra representedness hypothesis
is imposed on its computed output; the proof comes from
the existing fully typed source word's own target. -/
noncomputable def originalCompletedRealTermHiddenValue
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i)
    (d : OriginalRealNamedTermChoice S H sap nr2 i) :
    OriginalCompletedNamedHiddenValue S H :=
  ⟨originalRealNamedTermChoiceValue S H sap nr2 x d,
    ⟨d.2.2.1,rfl⟩⟩

/-- Likewise a term starting at an orphan hidden quotient
class evaluates into a genuinely represented named hidden
target, without adjoining any old real representative. -/
noncomputable def originalCompletedHiddenTermHiddenValue
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val)
    (d : OriginalHiddenNamedTermChoice S H sap nr2 D) :
    OriginalCompletedNamedHiddenValue S H :=
  ⟨originalHiddenNamedTermChoiceValue S H sap nr2 D q d,
    ⟨d.2.1,rfl⟩⟩

/-- Actual real generator and ALL its genuine named
real-to-hidden term values, in the complete interpreted
carrier, with true old equality as the sole real identity. -/
def originalCompletedRealGeneratedValues
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    Set (OriginalCompletedNamedCarrier S H) :=
  {Sum.inl (⟨i,x⟩ : Sigma X)} ∪
    (Sum.inr '' Set.range
      (originalCompletedRealTermHiddenValue S H sap nr2 x))

/-- Actual orphan quotient generator and ALL its genuinely
named hidden-to-hidden term values in the SAME completed
carrier, with no point in the old real summand. -/
def originalCompletedHiddenGeneratedValues
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    Set (OriginalCompletedNamedCarrier S H) :=
  Sum.inr '' Set.range
    (originalCompletedHiddenTermHiddenValue S H sap nr2 D q)

/-- Each real generator's complete named TERM-VALUE set in
the true represented terminal carrier has the same fixed
uniform m_typ bound as its underlying original normal codes.
There is no assumption on the number of real or hidden points. -/
theorem original_completed_real_generated_values_uniform
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    (originalCompletedRealGeneratedValues S H sap nr2 x).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  have hTargetFinite :
      (originalRealOneGeneratedNamedValues S H sap nr2 x).Finite := by
    unfold originalRealOneGeneratedNamedValues
    exact (Set.finite_singleton _).union
      ((original_real_named_term_values_finite S H sap nr2 x).image Sum.inr)
  letI : Finite ↥(originalRealOneGeneratedNamedValues
      S H sap nr2 x) := hTargetFinite.to_subtype
  have hSmall :
      (originalCompletedRealGeneratedValues S H sap nr2 x).ncard ≤
      (originalRealOneGeneratedNamedValues S H sap nr2 x).ncard := by
    apply Set.ncard_le_ncard_of_injOn
      (s := originalCompletedRealGeneratedValues S H sap nr2 x)
      (t := originalRealOneGeneratedNamedValues S H sap nr2 x)
      (originalCompletedCarrierForget S H)
    · intro z hz
      rcases hz with hz | hz
      · have heq : z = Sum.inl (⟨i,x⟩ : Sigma X) :=
          Set.mem_singleton_iff.mp hz
        subst z
        exact Or.inl rfl
      · rcases hz with ⟨v, ⟨d,rfl⟩,rfl⟩
        exact Or.inr
          ⟨originalRealNamedTermChoiceValue S H sap nr2 x d,
            ⟨d,rfl⟩,rfl⟩
    · intro a _ b _ h
      exact originalCompletedCarrierForget_injective S H h
  exact hSmall.trans
    (original_real_one_generated_named_values_uniform S H sap nr2 x)

/-- Orphan quotient-only generators satisfy the SAME uniform
bound in the real-or-represented-hidden carrier. In particular
no extra source real vertex is inserted by the proof. -/
theorem original_completed_hidden_generated_values_uniform
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    (originalCompletedHiddenGeneratedValues S H sap nr2 D q).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  have hTargetFinite :
      (originalHiddenOneGeneratedNamedValues S H sap nr2 D q).Finite := by
    unfold originalHiddenOneGeneratedNamedValues
    exact (original_hidden_named_term_values_finite
      S H sap nr2 D q).image Sum.inr
  letI : Finite ↥(originalHiddenOneGeneratedNamedValues
      S H sap nr2 D q) := hTargetFinite.to_subtype
  have hSmall :
      (originalCompletedHiddenGeneratedValues S H sap nr2 D q).ncard ≤
      (originalHiddenOneGeneratedNamedValues S H sap nr2 D q).ncard := by
    apply Set.ncard_le_ncard_of_injOn
      (s := originalCompletedHiddenGeneratedValues S H sap nr2 D q)
      (t := originalHiddenOneGeneratedNamedValues S H sap nr2 D q)
      (originalCompletedCarrierForget S H)
    · rintro z ⟨v, ⟨d,rfl⟩,rfl⟩
      exact ⟨originalHiddenNamedTermChoiceValue S H sap nr2 D q d,
        ⟨d,rfl⟩,rfl⟩
    · intro a _ b _ h
      exact originalCompletedCarrierForget_injective S H h
  exact hSmall.trans
    (original_hidden_one_generated_named_values_uniform
      S H sap nr2 D q)

end CCO.UnaryTermsReturn
