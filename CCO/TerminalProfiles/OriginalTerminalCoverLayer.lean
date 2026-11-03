import CCO.TransitionClosure.OriginalTerminalUniqueCoverReadout
import CCO.TerminalLattice.OriginalFullExternalLayer
import CCO.PositiveWords

/-!
# B051 — source09 terminal cover-layer reachability on the ORIGINAL source

The terminal FULL original-NR2 hypothesis supplies an actual equality-
inclusive RAW word for each invariant equivalence. For J > Id,
the accepted B049 original SAP injectivisation constructs one positive
OLD STRONG word for J°, with all arbitrary typed interior sorts retained.
Only THEN does the accepted independent B050 FULL old-cover external-layer
provider yield ONE positive OLD word for K minus J, including index two.

The second theorem constructs K = J+ and its full uniqueness from
the true FULL original finite invariant-equivalence lattice; it does not
pass an already chosen cover as an additional source hypothesis.

Original semantic HOM CCO is required by the B050 external-layer provider
but NOT silently by the B011 RAW-word or B049 SAP-normalization steps.
No hidden/quotient SAP, extra full equiv lattice, exact theta premise,
synthetic identity diversity letter or new axiom.
-/

universe u v w t

namespace CCO.TerminalProfiles

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original
open CCO.TerminalLattice
open CCO.TransitionClosure

/-- SOURCE09 C23–C25, a local FULL actual old cover J⋖K:
original terminal NR2 and SAP provide one positive word for J°, then
the accepted original HOM-CCO/SAP B050 provider supplies exactly the
diversity external layer K°\\J° by ONE positive old typed word.
Its word profile is genuinely nonempty, including index two. -/
theorem original_terminal_full_cover_layer_word
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J K : ColourEq S i)
    (hJK : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); J ⋖ K)
    (hJ : (⊥ : ColourEq S i) < J) :
    ∃ word : PositiveWord S i i,
      PositiveWord.profile S word =
        originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J ∧
      (PositiveWord.profile S word).Nonempty := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  obtain ⟨wJ, hwJ⟩ :=
    original_nonzero_equiv_positive_word_of_terminalNR2
      S H sap nr2 J hJ
  obtain ⟨word, hwWord⟩ :=
    original_full_cover_external_layer_positive_word
      S H sap cco J K hJK hJ wJ hwJ
  exact ⟨word, hwWord,
    PositiveWord.profile_nonempty_of_SAP S H sap word⟩

/-- SOURCE09 selected `thm:typed-cover-layer-reachable`:
for an ACTUAL nonzero proper meet-irreducible in the whole original
invariant-equivalence lattice, construct its unique full cover J+,
and reach ALL of K\\J as one positive STRONG original typed word.
Terminal NR2 separately makes the full relation RAW represented, so
the statement also receives the represented terminal source theorem,
without assuming a particular K or strengthening to quotient SAP. -/
theorem original_terminal_full_MI_cover_layer_reachable
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J) :
    ∃ K : ColourEq S i,
      (letI : Lattice (ColourEq S i) :=
        ColourEq.lattice S H (i := i); J ⋖ K) ∧
      (∀ L : ColourEq S i,
        (letI : Lattice (ColourEq S i) :=
          ColourEq.lattice S H (i := i); J ⋖ L) → L = K) ∧
      ∃ word : PositiveWord S i i,
        PositiveWord.profile S word =
          originalEquivDiversityPalette S K \
            originalEquivDiversityPalette S J ∧
        (PositiveWord.profile S word).Nonempty := by
  letI : Lattice (ColourEq S i) := ColourEq.lattice S H (i := i)
  obtain ⟨K, hJK, hUnique⟩ :=
    original_full_infIrred_exists_unique_cover S H J hMI
  obtain ⟨word, hw, hPositive⟩ :=
    original_terminal_full_cover_layer_word
      S H sap cco nr2 J K hJK hJ
  exact ⟨K, hJK, hUnique, word, hw, hPositive⟩

end CCO.TerminalProfiles
