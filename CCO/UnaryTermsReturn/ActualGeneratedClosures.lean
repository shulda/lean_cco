import CCO.UnaryTermsReturn.NormalCodeCoverage
import CCO.UnaryTermsReturn.TermValues
import Mathlib.Data.Set.Card

/-!
# B052 C11–C15: uniform finite ACTUAL one-generator value bounds

Each actual named real-source or orphan hidden-source unary term
value is represented by one of the FIXED finitely many original
RAW normal codes of B049. The code type depends only on the
finitely many original sort tags, full invariant equivalences
and invariant RAW relation tables, never on input vertices,
the number of actual quotient classes, or term syntax length.

The REAL generator itself is the one additional true original
identity value. All other generated positions are interpreted
quotient classes tagged by their actual FULL original kernel.
For an orphan hidden generator, there is NO real generator at
all: we use a real quotient representative only in a proof.

This constructs a UNIFORM NUMERICAL upper bound on these literal
actual unary term-value sets. The full induced hidden binary
diagram and the transfer through unary-admissible partial
structures remain separately identified receiving obligations.
No bound is asserted on arbitrary partial total-unary inputs.
-/

universe u v w t

namespace CCO.UnaryTermsReturn

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TransitionClosure
open CCO.ParityHasse.Original

/-- All genuinely NAMED real-to-hidden compositions, including
their actual real source projection and unbounded remaining
named quotient word, with every target OLD sort retained. -/
abbrev OriginalRealNamedTermChoice
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S) (i : ι) :=
  Σ j : ι, OriginalNamedRawUnaryTermDatum S H sap nr2 i j

/-- Actual semantic value of an entire real-source named term:
first the genuine real J-projection, then the given named word.
The output is the true OLD target sort/full kernel quotient tag. -/
noncomputable def originalRealNamedTermChoiceValue
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i)
    (d : OriginalRealNamedTermChoice S H sap nr2 i) :
    OriginalNormalCodeTargetValue S :=
  ⟨d.1, originalRealToHiddenNamedTermValue S H sap nr2 x d.2⟩

/-- Every actually interpreted real-source hidden value
belongs to the image of the SAME fixed, finite original
normal-code family; this is an EXACT source-to-function
consequence of B049's arbitrarily long term normalisation. -/
theorem original_real_named_term_values_subset_normal_codes
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    Set.range (originalRealNamedTermChoiceValue S H sap nr2 x) ⊆
      Set.range (originalSourceNormalCodeValue S H x) := by
  rintro z ⟨d,rfl⟩
  obtain ⟨j,⟨D,⟨F,w⟩⟩⟩ := d
  exact original_real_named_term_value_has_normal_code
    S H sap nr2 D F w x

theorem original_real_named_term_values_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    (Set.range
      (originalRealNamedTermChoiceValue S H sap nr2 x)).Finite :=
  (original_source_normal_code_values_finite S H x).subset
    (original_real_named_term_values_subset_normal_codes
      S H sap nr2 x)

/-- One original named HIDDEN generator has a fixed source
represented quotient D, but its target sort and coordinate
are unrestricted, subject only to the actual named syntax. -/
abbrev OriginalHiddenNamedTermChoice
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i) :=
  Σ j : ι, OriginalHiddenToHiddenNamedTermDatum S H sap nr2 D j

noncomputable def originalHiddenNamedTermChoiceValue
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val)
    (d : OriginalHiddenNamedTermChoice S H sap nr2 D) :
    OriginalNormalCodeTargetValue S :=
  ⟨d.1, originalHiddenToHiddenNamedTermValue
    S H sap nr2 D q d.2⟩

/-- Orphan quotient generators have the SAME bounded normal-code
image as a genuine old real REPRESENTATIVE in the ambient
quotient. The proof does NOT insert that representative into
a finite orphan substructure. -/
theorem original_hidden_named_term_values_subset_normal_codes
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    Set.range (originalHiddenNamedTermChoiceValue
        S H sap nr2 D q) ⊆
      (⋃ x : X i, Set.range (originalSourceNormalCodeValue S H x)) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      rintro z ⟨d,rfl⟩
      obtain ⟨j,⟨F,w⟩⟩ := d
      have hCode :=
        original_real_named_term_value_has_normal_code
          S H sap nr2 D F w x
      exact Set.mem_iUnion.mpr ⟨x,hCode⟩

/-- A STRONGER pointwise version, after choosing a literal
ambient old representative x: all named terms on its D-class
land in the SINGLE x-code image, with no union over infinitely
many representatives and hence a UNIFORM finite bound. -/
theorem original_hidden_named_term_values_subset_fixed_rep
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (x : X i) :
    Set.range (originalHiddenNamedTermChoiceValue
        S H sap nr2 D (Quotient.mk D.val.val x)) ⊆
      Set.range (originalSourceNormalCodeValue S H x) := by
  rintro z ⟨d,rfl⟩
  obtain ⟨j,⟨F,w⟩⟩ := d
  exact original_real_named_term_value_has_normal_code
    S H sap nr2 D F w x

theorem original_hidden_named_term_values_finite
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    (Set.range (originalHiddenNamedTermChoiceValue
      S H sap nr2 D q)).Finite := by
  induction q using Quotient.inductionOn with
  | _ x =>
      exact (original_source_normal_code_values_finite S H x).subset
        (original_hidden_named_term_values_subset_fixed_rep
          S H sap nr2 D x)

/-- A uniform CARDINALITY bound on the actual finite evaluated
normal-code set. All source sorts have one common fixed finite
code supertype; we count its cardinality rather than syntax. -/
theorem original_normal_code_values_ncard_uniform
    (H : HomogeneousSource S G)
    {i : ι} (x : X i) :
    (Set.range (originalSourceNormalCodeValue S H x)).ncard ≤
      Nat.card (OriginalAllNormalCodes S (G := G)) := by
  classical
  letI : Finite (OriginalSourceNormalCode S (G := G) i) :=
    original_source_normal_codes_finite S H i
  letI : Finite (OriginalAllNormalCodes S (G := G)) :=
    original_all_normal_codes_finite S H
  have hRange :
      (Set.range (originalSourceNormalCodeValue S H x)).ncard ≤
        Nat.card (OriginalSourceNormalCode S (G := G) i) := by
    have hh := Set.ncard_image_le
      (f := originalSourceNormalCodeValue S H x)
      (s := (Set.univ :
        Set (OriginalSourceNormalCode S (G := G) i)))
    simpa only [Set.image_univ, Set.ncard_univ] using hh
  have hInjective : Function.Injective
      (fun c : OriginalSourceNormalCode S (G := G) i =>
        (⟨i,c⟩ : OriginalAllNormalCodes S (G := G))) := by
    intro a b heq
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
  have hCard :
      Nat.card (OriginalSourceNormalCode S (G := G) i) ≤
        Nat.card (OriginalAllNormalCodes S (G := G)) := by
    have h :=
      Set.ncard_le_ncard_of_injOn
        (s := (Set.univ :
          Set (OriginalSourceNormalCode S (G := G) i)))
        (t := (Set.univ :
          Set (OriginalAllNormalCodes S (G := G))))
        (fun c : OriginalSourceNormalCode S (G := G) i =>
          (⟨i,c⟩ : OriginalAllNormalCodes S (G := G)))
        (by intro a ha; trivial)
        (by intro a ha b hb eq; exact hInjective eq)
    simpa only [Set.ncard_univ] using h
  exact hRange.trans hCard

/-- B052 actual quantitative UNIFORM bound for values of ALL
named real-source terms, including arbitrarily long inverse
and upward loops and all original target sort tags.
The source real identity is deliberately added separately. -/
theorem original_real_named_term_values_ncard_uniform
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    (Set.range
      (originalRealNamedTermChoiceValue S H sap nr2 x)).ncard ≤
      Nat.card (OriginalAllNormalCodes S (G := G)) := by
  exact (Set.ncard_le_ncard
    (original_real_named_term_values_subset_normal_codes S H sap nr2 x)
    (original_source_normal_code_values_finite S H x)).trans
      (original_normal_code_values_ncard_uniform S H x)

/-- The same fixed full-code budget also bounds every actual
orphan hidden-source generator, with the real representative
chosen only within the proof on the ambient quotient. -/
theorem original_hidden_named_term_values_ncard_uniform
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    (Set.range
      (originalHiddenNamedTermChoiceValue S H sap nr2 D q)).ncard ≤
      Nat.card (OriginalAllNormalCodes S (G := G)) := by
  induction q using Quotient.inductionOn with
  | _ x =>
      exact (Set.ncard_le_ncard
        (original_hidden_named_term_values_subset_fixed_rep
          S H sap nr2 D x)
        (original_source_normal_code_values_finite S H x)).trans
          (original_normal_code_values_ncard_uniform S H x)

/-- The genuine actual one-generated real source VALUE SET is
the real identity point together with every possible actual
hidden named term value. There is no quotient-to-real symbol,
so all nonidentity real-source values are quotient coordinates. -/
def originalRealOneGeneratedNamedValues
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    Set ((Sigma X) ⊕ OriginalNormalCodeTargetValue S) :=
  {Sum.inl (⟨i,x⟩ : Sigma X)} ∪
    (Sum.inr '' Set.range
      (originalRealNamedTermChoiceValue S H sap nr2 x))

/-- Real identity accounts for AT MOST one extra value.
For all genuine named terms from ANY original real sort,
actual original one-generated value sets satisfy a SINGLE
global source-bound m_typ, irrespective of their carrier sizes. -/
theorem original_real_one_generated_named_values_uniform
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (x : X i) :
    (originalRealOneGeneratedNamedValues S H sap nr2 x).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  let values := Set.range
    (originalRealNamedTermChoiceValue S H sap nr2 x)
  have hFinite : values.Finite :=
    original_real_named_term_values_finite S H sap nr2 x
  have hRangeBound :
      values.ncard ≤ Nat.card (OriginalAllNormalCodes S (G := G)) :=
    original_real_named_term_values_ncard_uniform S H sap nr2 x
  calc
    (originalRealOneGeneratedNamedValues S H sap nr2 x).ncard =
        ({Sum.inl (⟨i,x⟩ : Sigma X)} ∪
          (Sum.inr '' values)).ncard := rfl
    _ ≤ ({Sum.inl (⟨i,x⟩ : Sigma X)} :
           Set ((Sigma X) ⊕ OriginalNormalCodeTargetValue S)).ncard +
          (Sum.inr '' values).ncard := Set.ncard_union_le _ _
    _ ≤ 1 + values.ncard := by
      have hh := Set.ncard_image_le
        (f := (Sum.inr : OriginalNormalCodeTargetValue S →
          ((Sigma X) ⊕ OriginalNormalCodeTargetValue S)))
        (s := values) hFinite
      simpa only [Set.ncard_singleton] using Nat.add_le_add_left hh 1
    _ ≤ 1 + Nat.card (OriginalAllNormalCodes S (G := G)) :=
      Nat.add_le_add_left hRangeBound 1
    _ = originalSourceUniformNormalCodeBudget S H := by
      simp only [originalSourceUniformNormalCodeBudget, Nat.add_comm]


/-- The complete ACTUAL hidden-source one-generated term-VALUE set,
embedded in the same real-or-quotient tagged ambient carrier used for
real generators. An orphan quotient generator contributes NO real points:
choosing an old real representative in a proof never inserts it here. -/
def originalHiddenOneGeneratedNamedValues
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    Set ((Sigma X) ⊕ OriginalNormalCodeTargetValue S) :=
  Sum.inr '' Set.range
    (originalHiddenNamedTermChoiceValue S H sap nr2 D q)

/-- The SAME fixed global m_typ controls genuine orphan quotient
one-generator values on the complete tagged real/hidden carrier.
The bound is on interpreted named term FUNCTIONS, not on words;
no extra source real vertex is added to a quotient-only member. -/
theorem original_hidden_one_generated_named_values_uniform
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (D : OriginalNamedHiddenCoordinate S H i)
    (q : Quotient D.val.val) :
    (originalHiddenOneGeneratedNamedValues S H sap nr2 D q).ncard ≤
      originalSourceUniformNormalCodeBudget S H := by
  let values := Set.range
    (originalHiddenNamedTermChoiceValue S H sap nr2 D q)
  have hFinite : values.Finite :=
    original_hidden_named_term_values_finite S H sap nr2 D q
  have hBound :
      values.ncard ≤ Nat.card (OriginalAllNormalCodes S (G := G)) :=
    original_hidden_named_term_values_ncard_uniform S H sap nr2 D q
  calc
    (originalHiddenOneGeneratedNamedValues S H sap nr2 D q).ncard =
        (Sum.inr '' values :
          Set ((Sigma X) ⊕ OriginalNormalCodeTargetValue S)).ncard := rfl
    _ ≤ values.ncard :=
      Set.ncard_image_le
        (f := (Sum.inr : OriginalNormalCodeTargetValue S →
          ((Sigma X) ⊕ OriginalNormalCodeTargetValue S)))
        (s := values) hFinite
    _ ≤ Nat.card (OriginalAllNormalCodes S (G := G)) := hBound
    _ ≤ originalSourceUniformNormalCodeBudget S H := by
      change Nat.card (OriginalAllNormalCodes S (G := G)) ≤
        Nat.card (OriginalAllNormalCodes S (G := G)) + 1
      exact Nat.le_add_right _ _

end CCO.UnaryTermsReturn
