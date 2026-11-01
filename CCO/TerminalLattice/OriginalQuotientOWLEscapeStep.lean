import CCO.TerminalLattice.OriginalQuotientHellyEscape
import CCO.TerminalLattice.OriginalQuotientStatePowers

/-!
# B050 source09 OWL: a genuine finite positive quotient escape transition

This module packages the SOURCE contradiction's precise finite
state space. A state is one ORIGINAL-G-invariant binary relation on
the actual J quotient, whose ENTIRE old diversity pullback has one
genuine positive typed original word, which is nonempty, lies in the
true K/J equivalence and avoids the chosen complete reset orbital M0.
The state MAY contain the genuine quotient diagonal.

Under the source's temporary no-mixed-full-product contradiction,
the already proved ORIGINAL CCO+SAP finite positive-word 2-Helly
gives a complete external original-G orbital C with R disjoint from
M0;C. Peirce symmetry now proves R;C disjoint from M0.
The actual invariant composition, original positive-word
semigroup, old upper equivalence and seriality supply all state
invariants for this successor.

No quotient-reduct action, extra CCO, invented finite quotient
carrier, reset as a hypothesis, or hidden diagonal deletion.
The finite-state recurrence/periodic-product contradiction
remains a separate step.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- The exact finite SOURCE OWL escape state. The group is the
ORIGINAL ambient G on actual J classes. The last condition
excludes the complete reset orbit but never excludes the true
quotient diagonal. The positivity condition is an actual original
typed word with the FULL old diversity pullback as its profile. -/
def OriginalOWLEscapeState
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b : X i) :=
  {R : OriginalInvariantQuotientState S H J //
    OriginalPositiveQuotientState S J R.val ∧
    (∃ q r : Quotient J.val, R.val q r) ∧
    (∀ q r : Quotient J.val, R.val q r →
      originalUpperSetoid S J K hJK q r) ∧
    (∀ q r : Quotient J.val, R.val q r →
      ¬ originalQuotientOrbital S (G := G) J a b q r)}

/-- These exact positive escape states form a finite type although
the actual J quotient carrier itself may be infinite. This
finiteness is inherited from the proved finite optional fine-atom
truth table for ORIGINAL-G-invariant binary relations. -/
noncomputable instance originalOWLEscapeState_finite
    (H : HomogeneousSource S G)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (a b : X i) :
    Finite (OriginalOWLEscapeState S H J K hJK a b) := by
  letI : Finite (OriginalInvariantQuotientState S H J) :=
    originalInvariantQuotientState_finite S H J
  exact Finite.of_injective
    (fun R : OriginalOWLEscapeState S H J K hJK a b => R.val)
    Subtype.val_injective

/-- An ACTUAL different complete K-external old-G orbital supplies
a real initial positive escape state, including a chosen pair to
witness nonemptiness. Disjointness from M0 uses complete orbit
equality upon overlap, not a fabricated quotient orbit partition. -/
def originalOWLEscapeState_initial
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (a b c d : X i)
    (hKcd : K c d) (hNotJcd : ¬ J c d)
    (hDifferent :
      originalQuotientOrbital S (G := G) J c d ≠
        originalQuotientOrbital S (G := G) J a b) :
    OriginalOWLEscapeState S H J K hJK a b := by
  let C : OriginalExternalQuotientState S H J K :=
    originalExternalQuotientState_of_pair S H J K c d hKcd hNotJcd
  refine ⟨C.val, ?_, ?_, ?_, ?_⟩
  · exact originalExternalQuotientState_positive
      S H sap J K hJ wJ hwJ C
  · exact ⟨Quotient.mk J.val c, Quotient.mk J.val d,
      originalQuotientOrbital_root S (G := G) J c d⟩
  · exact originalQuotientOrbital_inside_originalUpper
      S H J K hJK c d hKcd
  · intro q r hC hM
    apply hDifferent
    exact originalQuotientOrbital_eq_of_overlap
      S H J c d a b q r hC hM

/-- ONE SOURCE OWL escape transition. Under the genuine
no-mixed-full contradiction premise, every actual positive,
nonempty, upper-K and M0-disjoint state R has SOME complete
external orbital C for which the literal composition R;C
is again an actual state of exactly the same finite type.
No ready successor, nonempty arbitrary relation, or Helly
provider is postulated. -/
theorem originalOWLEscapeState_successor
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ≤ K) (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (a b : X i) (hab : K a b) (hNotJab : ¬ J a b)
    (hReset : RawSymmetric.compose
      (originalQuotientOrbital S (G := G) J a b)
      (originalQuotientOrbital S (G := G) J a b) =
        (originalUpperSetoid S J K hJK).r)
    (hDifferent : ∃ c d : X i, K c d ∧ ¬ J c d ∧
      originalQuotientOrbital S (G := G) J c d ≠
        originalQuotientOrbital S (G := G) J a b)
    (hNoMixedFull : ∀ c d : X i, K c d → ¬ J c d →
      originalQuotientOrbital S (G := G) J c d ≠
        originalQuotientOrbital S (G := G) J a b →
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J c d) ≠
        originalQuotientExternalLayer S J K hJK)
    (R : OriginalOWLEscapeState S H J K hJK a b) :
    ∃ C : OriginalExternalQuotientState S H J K,
      ∃ T : OriginalOWLEscapeState S H J K hJK a b,
        T.val.val = RawSymmetric.compose R.val.val C.val.val := by
  obtain ⟨c,d,hKcd,hNotJcd,hAvoid⟩ :=
    original_positive_quotient_state_escape
      S H sap cco J K hJK hJ wJ hwJ a b hab hNotJab
        hReset hDifferent hNoMixedFull R.val R.property.1
          R.property.2.1 R.property.2.2.2
  let C : OriginalExternalQuotientState S H J K :=
    originalExternalQuotientState_of_pair S H J K c d hKcd hNotJcd
  let T : OriginalInvariantQuotientState S H J :=
    originalInvariantQuotientState_comp S H J R.val C.val
  have hPositiveC : OriginalPositiveQuotientState S J C.val.val :=
    originalExternalQuotientState_positive
      S H sap J K hJ wJ hwJ C
  have hPositiveT : OriginalPositiveQuotientState S J T.val :=
    original_positive_quotient_state_comp S H sap J hJ
      R.val.val C.val.val R.property.1 hPositiveC
  have hNonemptyT : ∃ q r : Quotient J.val, T.val q r := by
    obtain ⟨q,mid,hRmid⟩ := R.property.2.1
    obtain ⟨r,hCr⟩ := originalExternalQuotientState_serial S H J K C mid
    exact ⟨q,r,mid,hRmid,hCr⟩
  have hInsideT : ∀ q r : Quotient J.val, T.val q r →
      originalUpperSetoid S J K hJK q r := by
    intro q r
    rintro ⟨mid,hRmid,hCmid⟩
    exact (originalUpperSetoid S J K hJK).trans
      (R.property.2.2.1 q mid hRmid)
      (originalQuotientOrbital_inside_originalUpper
        S H J K hJK c d hKcd mid r hCmid)
  have hDisjointT : ∀ q r : Quotient J.val, T.val q r →
      ¬ originalQuotientOrbital S (G := G) J a b q r := by
    intro q r
    rintro ⟨mid,hRmid,hCmid⟩ hM
    have hReverse : C.val.val r mid :=
      originalQuotientOrbital_symmetric S H J c d mid r hCmid
    apply hAvoid
    refine ⟨q,mid,hRmid,?_⟩
    exact ⟨r,hM,hReverse⟩
  refine ⟨C, ⟨T, hPositiveT, hNonemptyT, hInsideT, hDisjointT⟩, ?_⟩
  rfl

end CCO.TerminalLattice
