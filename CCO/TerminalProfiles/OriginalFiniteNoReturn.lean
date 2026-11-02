import CCO.TerminalProfiles.OriginalTerminalNoReturn
import CCO.StrongExact.ProfileSemantics

/-!
# B051 TNR C12: no-return for ANY finite NONEMPTY positive product

A sequence of actual old positive typed a–a words has a positive
diversity product without adjoined zero-length STRONG identity. The
first factor and the genuinely nonempty product of all remaining
factors meet the locally proved original no-return theorem, and the
argument iterates. All positive products are genuinely nonempty
because original visible SAP provides real point gluing.

No CCO, hidden quotient SAP, mixed sort commutation, artificial
identity factor, or global NR2 is introduced. The local source
exclusion of a strict two-class interval above J remains sufficient.
-/

universe u v w t

namespace CCO.TerminalProfiles

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.ParityHasse.Original
open CCO.TerminalLattice

/-- Actual finite NONEMPTY product of same-sort OLD positive word
profiles, with no zero-factor or identity-labelled STRONG edge. -/
def originalPositiveListProduct {i : ι} :
    PositiveWord S i i → List (PositiveWord S i i) → S.Menu i i
  | first, [] => PositiveWord.profile S first
  | first, second :: rest =>
      S.product (PositiveWord.profile S first)
        (originalPositiveListProduct second rest)

/-- Every nonempty finite list-product has a genuinely witnessed
original STRONG diversity atom, using actual original SAP. -/
theorem originalPositiveListProduct_nonempty
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (first : PositiveWord S i i)
    (rest : List (PositiveWord S i i)) :
    (originalPositiveListProduct S first rest).Nonempty := by
  induction rest generalizing first with
  | nil =>
      exact PositiveWord.profile_nonempty_of_SAP S H sap first
  | cons second tail ih =>
      change (S.product (PositiveWord.profile S first)
        (originalPositiveListProduct S second tail)).Nonempty
      exact CCO.StrongExact.product_nonempty_of_SAP
        S H sap (PositiveWord.profile S first)
        (originalPositiveListProduct S second tail)
        (PositiveWord.profile_nonempty_of_SAP S H sap first)
        (ih second)

/-- SOURCE09 C12: if one finite, nonempty original STRONG
same-sort product lies in J°, then EVERY actual positive word
factor lies within J°. Only the local full original cut exclusion
of a two-class relative interval above J is used. A one-factor
product is handled by its own premise, never by an invented unit. -/
theorem original_finite_no_return_of_local_no_two
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (_hJ : (⊥ : ColourEq S i) < J)
    (hNoTwo : ∀ K : ColourEq S i, J < K →
      ¬ CCO.Selectors.RelativeIndexTwo J.val K.val)
    (first : PositiveWord S i i)
    (rest : List (PositiveWord S i i))
    (hProduct : originalPositiveListProduct S first rest ⊆
      originalEquivDiversityPalette S J) :
    PositiveWord.profile S first ⊆ originalEquivDiversityPalette S J ∧
      ∀ w ∈ rest,
        PositiveWord.profile S w ⊆
          originalEquivDiversityPalette S J := by
  induction rest generalizing first with
  | nil =>
      exact ⟨hProduct, by intro w hw; cases hw⟩
  | cons second tail ih =>
      have hPair :
          PositiveWord.profile S first ⊆
            originalEquivDiversityPalette S J ∧
          originalPositiveListProduct S second tail ⊆
            originalEquivDiversityPalette S J := by
        apply original_no_return_menus_of_local_no_two
          S H J hNoTwo
          (PositiveWord.profile S first)
          (originalPositiveListProduct S second tail)
          (PositiveWord.profile_nonempty_of_SAP S H sap first)
          (originalPositiveListProduct_nonempty S H sap second tail)
        exact hProduct
      obtain ⟨hSecond, hTail⟩ := ih second hPair.2
      refine ⟨hPair.1, ?_⟩
      intro w hw
      have hMember : w = second ∨ w ∈ tail := by
        simpa only [List.mem_cons] using hw
      rcases hMember with hEq | hMem
      · subst w
        exact hSecond
      · exact hTail w hMem

/-- Actual terminal FULL original NR2 is an instantiation of the
LOCAL cut hypothesis, not a substitute for a real no-return proof. -/
theorem original_terminal_finite_no_return
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (first : PositiveWord S i i)
    (rest : List (PositiveWord S i i))
    (hProduct : originalPositiveListProduct S first rest ⊆
      originalEquivDiversityPalette S J) :
    PositiveWord.profile S first ⊆ originalEquivDiversityPalette S J ∧
      ∀ w ∈ rest,
        PositiveWord.profile S w ⊆
          originalEquivDiversityPalette S J := by
  have hNoTwo : ∀ K : ColourEq S i, J < K →
      ¬ CCO.Selectors.RelativeIndexTwo J.val K.val := by
    intro K _ hTwo
    exact nr2 i J.val K.val J.property K.property hTwo
  exact original_finite_no_return_of_local_no_two
    S H sap J hJ hNoTwo first rest hProduct

end CCO.TerminalProfiles
