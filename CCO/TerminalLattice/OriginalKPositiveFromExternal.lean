import CCO.TerminalLattice.OriginalQuotientResetSquare
import CCO.TerminalLattice.CompleteOrbitalWord
import CCO.TerminalLattice.PositiveBranchCycles
import CCO.TerminalLattice.StrongPathReordering

/-!
# B050 source09 OWL: K-diversity positivity is DERIVED from a J-positive word

For the original external-layer theorem the source assumes only ONE
positive ORIGINAL J-diversity word, NOT a K-diversity word. Under a
FULL original cover J ⋖ K with local index different from two,
choose an actual external old pair. Its COMPLETE original-G
quotient orbital has an old positive typed word by the C23
J-saturation theorem. CCO-free FULL-cover eventual STRONG
orbital powers saturate K-diversity; concatenating finitely many
copies of that SAME genuine old positive word produces ONE
actual positive old word whose exact STRONG profile is K°.

This closes the missing positive K° premise for the source C40
single-network reset, without inventing old identity, quotient SAP,
NR2, additional CCO or new external word assumptions.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Original source09 seed: a genuinely non-J old K-external real
pair and the one positive J° word produce a positive ORIGINAL
same-sort typed word for FULL K-diversity. Intermediate sorts
of its atomic letters are exactly those of the source word.
No positive K-word is a theorem input. -/
theorem original_Kpositive_from_external_orbital_powers
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ⋖ K) (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (a b : X i) (hab : K a b) (hne : ¬ J a b)
    (hNotTwo : relativeIndex J.val K.val a ≠ 2) :
    ∃ wK : PositiveWord S i i,
      PositiveWord.profile S wK =
        originalEquivDiversityPalette S K := by
  have hneAB : a ≠ b := by
    intro heq
    subst b
    exact hne (J.val.refl a)
  have hTag : (⟨i,a⟩ : Sigma X) ≠ ⟨i,b⟩ := by
    intro heq
    have habEq : a = b := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
    exact hneAB habEq
  obtain ⟨tAtom,hCol⟩ := S.some_colour_of_ne a b hTag
  obtain ⟨word,hWord⟩ :=
    originalQuotientOrbital_positive_word
      S H sap J hJ wJ hwJ tAtom a b hCol
  obtain ⟨N,hN,hPowers⟩ :=
    originalQuotient_uniform_strong_palette_powers
      S H sap J K hJK hJ a b hab hne hNotTwo
  let wK : PositiveWord S i i :=
    originalPositiveBranchPath S word (List.replicate (N-1) word)
  refine ⟨wK, ?_⟩
  calc
    PositiveWord.profile S wK =
        (List.replicate (N-1) (PositiveWord.profile S word)).foldl
          (fun A B => S.product A B)
          (PositiveWord.profile S word) := by
            simpa only [wK, List.map_replicate] using
              (originalPositiveBranchPath_profile S H sap word
                (List.replicate (N-1) word))
    _ = originalStrongPalettePower S
          (PositiveWord.profile S word) (N-1) :=
      original_strong_fold_replicate S
        (PositiveWord.profile S word) (N-1)
    _ = originalStrongPalettePower S
          (originalQuotientOrbitalPalette S (G := G) J a b) (N-1) := by
            rw [hWord]
    _ = originalEquivDiversityPalette S K := hPowers N le_rfl

/-- Source09 OWL reset seed: the FULL original quotient cover has an
actual external pair, and local index not two transfers from its
given original anchor by old homogeneity. The preceding positivity
construction therefore discharges the K-positive word premise
of C40, and the already proved original reset/strong-semi-group
bridge gives ONE complete old-G external quotient orbital M0
whose QUOTIENT relational square is literally K/J.

Assumes only source09's old positive J° word, original SAP/CCO,
full cover and the non-index-two branch. The index-two branch is
handled by the independent singleton-orbital theorem.
-/
theorem original_full_cover_quotient_reset_of_Jpositive
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ⋖ K) (hJ : (⊥ : ColourEq S i) < J)
    (anchor : X i)
    (hNotTwo : relativeIndex J.val K.val anchor ≠ 2)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J) :
    ∃ a b : X i, K a b ∧ ¬ J a b ∧
      RawSymmetric.compose
        (originalQuotientOrbital S (G := G) J a b)
        (originalQuotientOrbital S (G := G) J a b) =
          (originalUpperSetoid S J K hJK.le).r := by
  have hNotKJ : ¬ K ≤ J := not_le_of_gt hJK.lt
  have hExternal : ∃ a b : X i, K a b ∧ ¬ J a b := by
    by_contra hMissing
    apply hNotKJ
    intro a b hab
    by_contra hne
    exact hMissing ⟨a,b,hab,hne⟩
  obtain ⟨a,b,hab,hne⟩ := hExternal
  have hIndex :
      relativeIndex J.val K.val a =
        relativeIndex J.val K.val anchor :=
    relativeIndex_uniform S H J K a anchor
  have hNotTwoA : relativeIndex J.val K.val a ≠ 2 := by
    intro hh
    exact hNotTwo (hIndex.symm.trans hh)
  obtain ⟨wK,hwK⟩ :=
    original_Kpositive_from_external_orbital_powers
      S H sap J K hJK hJ wJ hwJ a b hab hne hNotTwoA
  exact original_full_cover_reset_quotient_square
    S H sap cco J K hJK hJ anchor hNotTwo
      wJ hwJ wK hwK

end CCO.TerminalLattice
