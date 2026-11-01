import CCO.TerminalLattice.OriginalQuotientOWLFiniteEscape
import CCO.TerminalLattice.OriginalQuotientPositiveHelly

/-!
# B050 source09 OWL: exact OLD positive word of the external quotient layer

The source has TWO distinct equality notions. The true external
quotient layer excludes the QUOTIENT J-diagonal, whereas its original
old atomic profile consists only of OLD diversity atoms whose endpoints
are K-related and NOT J-related. This file proves the exact relation
identity between those two formulations, using actual old real pairs
and the original J/K colour invariance.

Thus a genuine positive old word for the entire quotient external
relation becomes one positive original typed word with exact STRONG
endpoint profile K° minus J°. No source instance is asserted by an
unproved positive-state premise: the mixed complete-orbit product
construction discharges that premise through the already proved C23
old-G orbit word representations and old SAP quotient semigroup.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- The TRUE quotient external K/J layer, including its exclusion
of the quotient diagonal, has OLD diversity pullback equal to the
literal original fine-atom relation on K° minus J°. Here J° and K°
are menus of ORIGINAL diversity ATOMS, not quotient relations.
No source SAP or CCO is used. -/
theorem original_external_layer_fine_menu_semantics
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K) :
    S.menuRel
      (originalEquivDiversityPalette S K \
        originalEquivDiversityPalette S J) =
      quotientDiversity J.val (originalQuotientExternalLayer S J K hJK) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨c,⟨hcK,hcNotJ⟩,hColour⟩
    obtain ⟨u,v,hKuv,hColUV⟩ := hcK
    have hKxy : K x y :=
      (K.property u v x y (hColUV.trans hColour.symm)).mp hKuv
    have hNotJxy : ¬ J x y := by
      intro hJxy
      exact hcNotJ ⟨x,y,hJxy,hColour⟩
    have hne : x ≠ y := by
      intro hh
      exact S.atomRel_ne hColour (congrArg (Sigma.mk i) hh)
    exact ⟨hne,(originalUpperSetoid_mk S J K hJK x y).mpr hKxy,
      fun hEq => hNotJxy (Quotient.exact hEq)⟩
  · rintro ⟨hne,hUpper,hDifferent⟩
    have hKxy : K x y :=
      (originalUpperSetoid_mk S J K hJK x y).mp hUpper
    have hNotJxy : ¬ J x y := by
      intro hJxy
      exact hDifferent (Quotient.sound hJxy)
    have hTagged : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
      intro hh
      have hxy : x = y := by
        simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using hh
      exact hne hxy
    obtain ⟨c,hColour⟩ := S.some_colour_of_ne x y hTagged
    refine ⟨c,⟨⟨x,y,hKxy,hColour⟩,?_⟩,hColour⟩
    rintro ⟨u,v,hJuv,hColUV⟩
    have hJxy : J x y :=
      (J.property u v x y (hColUV.trans hColour.symm)).mp hJuv
    exact hNotJxy hJxy

/-- A FULL positive original typed word presenting the quotient
external layer has EXACT original fine STRONG endpoint menu
K° minus J°. This is a faithful conversion, not an assertion
that the needed quotient-positive state exists. -/
theorem original_external_layer_positive_word_of_state
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (hPositive : OriginalPositiveQuotientState S J
      (originalQuotientExternalLayer S J K hJK)) :
    ∃ word : PositiveWord S i i,
      PositiveWord.profile S word =
        originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J := by
  obtain ⟨word,hWord⟩ := hPositive
  refine ⟨word,?_⟩
  calc
    PositiveWord.profile S word =
        S.diversityGuard (S.menuRel (PositiveWord.profile S word)) :=
      (S.diversityGuard_menuRel _).symm
    _ = S.diversityGuard
          (quotientDiversity J.val
            (originalQuotientExternalLayer S J K hJK)) := by
      rw [hWord]
    _ = S.diversityGuard
          (S.menuRel
            (originalEquivDiversityPalette S K \
              originalEquivDiversityPalette S J)) := by
      rw [original_external_layer_fine_menu_semantics S J K hJK]
    _ = originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J :=
      S.diversityGuard_menuRel _

/-- SOURCE OWL mixed pair branch, now fully from REAL positive old
atomic words of two COMPLETE original-G external quotient orbitals.
If their quotient relation product is the entire external K/J layer,
concatenate their actual C23 old positive typed words. The proved
original SAP strong quotient-semigroup identity yields the WHOLE
external old diversity menu; a proper fine suborbit never replaces
either complete old-G orbital. -/
theorem original_external_layer_word_of_mixed_orbitals
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (a b c d : X i)
    (hKab : K a b) (hNotJab : ¬ J a b)
    (hKcd : K c d) (hNotJcd : ¬ J c d)
    (hMixed : RawSymmetric.compose
      (originalQuotientOrbital S (G := G) J a b)
      (originalQuotientOrbital S (G := G) J c d) =
        originalQuotientExternalLayer S J K hJK) :
    ∃ word : PositiveWord S i i,
      PositiveWord.profile S word =
        originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J := by
  let A : OriginalExternalQuotientState S H J K :=
    originalExternalQuotientState_of_pair S H J K a b hKab hNotJab
  let B : OriginalExternalQuotientState S H J K :=
    originalExternalQuotientState_of_pair S H J K c d hKcd hNotJcd
  have hA : OriginalPositiveQuotientState S J
      (originalQuotientOrbital S (G := G) J a b) :=
    originalExternalQuotientState_positive
      S H sap J K hJ wJ hwJ A
  have hB : OriginalPositiveQuotientState S J
      (originalQuotientOrbital S (G := G) J c d) :=
    originalExternalQuotientState_positive
      S H sap J K hJ wJ hwJ B
  have hProduct : OriginalPositiveQuotientState S J
      (RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J c d)) :=
    original_positive_quotient_state_comp
      S H sap J hJ _ _ hA hB
  rw [hMixed] at hProduct
  exact original_external_layer_positive_word_of_state
    S J K hJK hProduct

end CCO.TerminalLattice
