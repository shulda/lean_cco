import CCO.TerminalLattice.OriginalQuotientInvariantFinite
import CCO.TerminalLattice.QuotientSquareSaturation

/-!
# B050 source09 OWL: the actual original C40 reset squares ON THE QUOTIENT

The full original C40 one-network reset concludes that one COMPLETE
old-G quotient orbital's exact ORIGINAL fine-atom STRONG square equals
K-diversity. We convert this to its genuine quotient relational square
M0;M0 = K/J, including the TRUE quotient diagonal, via the source
C11/C12 full-diversity lift and its actual SAP-derived injectivity.

This is a theorem about the SAME original full group G acting on the
J-classes, not the automorphisms of a quotient reduct. No diagonal
atom is invented: it is the genuine old J-diversity fibre of the
quotient equality relation. The source C40 proof already performed
the ONE original global semantic CCO completion.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- The original STRONG equality of one complete external orbital
square with K° is exactly equivalent to the FULL quotient square
being K/J. This direction genuinely uses SAP to reflect the full
OLD diversity pullback through J; no quotient-level SAP is assumed.
-/
theorem original_quotient_square_full_of_strong
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i) (hJK : J ≤ K)
    (hJ : (⊥ : ColourEq S i) < J)
    (a b : X i)
    (hStrong :
      S.product
        (originalQuotientOrbitalPalette S (G := G) J a b)
        (originalQuotientOrbitalPalette S (G := G) J a b) =
          originalEquivDiversityPalette S K) :
    RawSymmetric.compose
      (originalQuotientOrbital S (G := G) J a b)
      (originalQuotientOrbital S (G := G) J a b) =
        (originalUpperSetoid S J K hJK).r := by
  let R : Quotient J.val → Quotient J.val → Prop :=
    originalQuotientOrbital S (G := G) J a b
  let T : S.Menu i i :=
    originalQuotientOrbitalPalette S (G := G) J a b
  apply original_quotient_pullback_injective S H sap J hJ
  calc
    quotientDiversity J.val (RawSymmetric.compose R R) =
        S.menuRel (S.product T T) :=
      (original_complete_quotient_orbital_square_semantics
        S H sap J hJ a b).symm
    _ = S.menuRel (originalEquivDiversityPalette S K) := by
      rw [hStrong]
    _ = quotientDiversity J.val
          (originalUpperSetoid S J K hJK).r := by
      rw [originalEquivDiversityPalette_semantics S K]
      funext x y
      apply propext
      change (x ≠ y ∧ K x y) ↔
        (x ≠ y ∧ originalUpperSetoid S J K hJK
          (Quotient.mk J.val x) (Quotient.mk J.val y))
      constructor
      · rintro ⟨hne,hK⟩
        exact ⟨hne,(originalUpperSetoid_mk S J K hJK x y).mpr hK⟩
      · rintro ⟨hne,hUpper⟩
        exact ⟨hne,(originalUpperSetoid_mk S J K hJK x y).mp hUpper⟩

/-- Source09 receives the actual original C40 reset and obtains
the promised COMPLETE external original-G quotient orbital M0 with
the true full relational square M0;M0=K/J. Only the source C40
hypotheses appear: no invented reset witness, quotient provider,
new axiom or second original CCO application. -/
theorem original_full_cover_reset_quotient_square
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ⋖ K) (hJ : (⊥ : ColourEq S i) < J)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (wK : PositiveWord S i i)
    (hwK : PositiveWord.profile S wK =
      originalEquivDiversityPalette S K) :
    ∃ a b : X i, K a b ∧ ¬ J a b ∧
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J a b) =
          (originalUpperSetoid S J K hJK.le).r := by
  obtain ⟨a,b,hab,hne,hStrong,_⟩ :=
    original_full_cover_reset_single_path
      S H sap cco J K hJK hJ anchor hNotTwo
        wJ hwJ wK hwK
  exact ⟨a,b,hab,hne,
    original_quotient_square_full_of_strong
      S H sap J K hJK.le hJ a b hStrong⟩

end CCO.TerminalLattice
