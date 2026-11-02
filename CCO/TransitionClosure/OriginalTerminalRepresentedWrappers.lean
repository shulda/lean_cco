import CCO.TransitionClosure.OriginalStrongExactPrime
import CCO.RealClosure.Bounds.TerminalNR2
import CCO.TerminalLattice.FibreSAP

/-!
# B049 source07 C19/C23: exact terminal represented original wrappers

These are the selected original-sort represented terminal consumers of the
ALREADY proved local FULL cover first-hit/strong exact prime theorems.

B011 terminal FULL original NR2 supplies an ACTUAL one-word RAW atomic
presentation for every full original ColourEq, including its logical
diagonal. For nonzero equivalences the positive-word normalization plus
original visible SAP yields a genuine positive STRONG OLD word for the
DIVERSITY palette. The identity equivalence has EMPTY diversity palette
and is handled as a vacuous case, never with a fake positive identity word.

For the prime-intersection consumer, B003's actual strongly completable
canonical PC domain is converted to an original finite positive-word meet
using the real accepted typed PC theorem, not by assuming an abstract
conditional exactness predicate.

No hidden/quotient SAP, terminality in the local first-hit theorem, new
CCO provider, synthetic strong identity or represented-subposet MI appears.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original
open CCO.TerminalLattice

/-- The true original identity setoid has no diversity fine atoms.
This is not a STRONG identity element. -/
theorem originalEquivDiversityPalette_bot {i : ι} :
    originalEquivDiversityPalette S (⊥ : ColourEq S i) =
      (∅ : S.Menu i i) := by
  change S.diversityGuard (TRel.ident X i) = (∅ : S.Menu i i)
  exact S.diversityGuard_ident i

/-- A NONIDENTITY FULL old invariant equivalence has ONE ACTUAL
positive STRONG old typed-word presentation under the source's
terminal FULL original NR2. First obtain the B011 equality-inclusive
RAW presentation, then delete logical identity letters and use
visible SAP for exact diversity-guard/STRONG profile equality.

The original J-diversity menu is nonempty by a genuinely distinct
old J-related pair, ruling out the empty RAW identity branch.
The word may visit arbitrary original named sorts internally. -/
theorem original_nonzero_equiv_positive_word_of_terminalNR2
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J) :
    ∃ p : PositiveWord S i i,
      PositiveWord.profile S p = originalEquivDiversityPalette S J := by
  obtain ⟨word, hWord⟩ :=
    RealClosure.Bounds.terminal_raw_word_of_originalNR2 S H nr2 J
  have hPalette : (originalEquivDiversityPalette S J).Nonempty := by
    obtain ⟨x,y,hJxy,hxy⟩ := actual_nontrivial_equiv_pair S J hJ
    have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
      intro h
      exact hxy (by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h)
    obtain ⟨a,hAtom⟩ := S.some_colour_of_ne x y hTag
    exact ⟨a, ⟨x,y,hJxy,hAtom⟩⟩
  have hGuard :
      S.diversityGuard (RawWord.relation S word) =
        originalEquivDiversityPalette S J := by
    rw [hWord]
    rfl
  rcases PositiveWord.raw_guard_empty_or_positive_profile_of_SAP
      S H sap word with hEmpty | ⟨p,hProfile⟩
  · rw [hGuard] at hEmpty
    obtain ⟨a,ha⟩ := hPalette
    rw [hEmpty] at ha
    exact False.elim (Set.not_mem_empty a ha)
  · exact ⟨p,hProfile.symm.trans hGuard⟩

/-- The exact represented version of the pinned C19 cover
interpolation: under terminal NR2 all FULL original equivalences
are genuinely represented, so the original full MI J and its
actual cover K can use the SOURCE07 original OWI theorem.

The special J=Id branch is vacuous (the positive STRONG P meets
no logical identity). No positive-J/K word is an EXTRA input:
both are constructed by B011, real SAP and the previous lemma. -/
theorem original_terminal_represented_cover_interpolation
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J K : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (hJK : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); J ⋖ K)
    (P : PositiveWord S i i)
    (hMeet : (PositiveWord.profile S P ∩
      originalEquivDiversityPalette S J).Nonempty)
    (hExit : ∃ a : S.Atom i i,
      a ∈ PositiveWord.profile S P ∧
      a ∉ originalEquivDiversityPalette S J) :
    (PositiveWord.profile S P ∩
      (originalEquivDiversityPalette S K \
        originalEquivDiversityPalette S J)).Nonempty := by
  by_cases hZero : J = ⊥
  · subst J
    rw [originalEquivDiversityPalette_bot S] at hMeet
    obtain ⟨a,_,ha⟩ := hMeet
    exact False.elim (Set.not_mem_empty a ha)
  · have hJ : (⊥ : ColourEq S i) < J :=
      lt_of_le_of_ne bot_le hZero.symm
    have hK : (⊥ : ColourEq S i) < K :=
      lt_of_lt_of_le hJ hJK.1.le
    obtain ⟨wJ,hwJ⟩ :=
      original_nonzero_equiv_positive_word_of_terminalNR2
        S H sap nr2 J hJ
    obtain ⟨wK,hwK⟩ :=
      original_nonzero_equiv_positive_word_of_terminalNR2
        S H sap nr2 K hK
    exact original_full_cover_positive_word_interpolation
      S H sap cco J K hMI hJK hJ wJ wK P hwJ hwK hMeet hExit

/-- SOURCE07 selected C23 typed prime intersection for ACTUAL
strong-PC fixed-point endpoint domains. Under terminal ORIGINAL
FULL NR2 the represented proper MI is literally a FULL original
ColourEq MI, with its unique full cover. The J=Id case is
impossible because the common STRONG diversity domain is nonempty.

B003's canonical typed PC-domain conversion (including empty
defining word lists, denoting diversity Top) supplies the exact
positive-profile family required by the already proved original
FULL strong-exact MI prime theorem. No Set-Pasch or hidden SAP. -/
theorem original_terminal_represented_prime_intersection
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    (nr2 : Selectors.OriginalNR2 S)
    {i : ι} (J K : ColourEq S i)
    (hMI : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); InfIrred J)
    (hJK : letI : Lattice (ColourEq S i) :=
      ColourEq.lattice S H (i := i); J ⋖ K)
    (A B : S.Menu i i)
    (hA : StrongExact.CanonicalThetaDomain S A)
    (hB : StrongExact.CanonicalThetaDomain S B)
    (hAB : (A ∩ B).Nonempty)
    (hInside : (A ∩ B) ⊆ originalEquivDiversityPalette S J) :
    A ⊆ originalEquivDiversityPalette S J ∨
      B ⊆ originalEquivDiversityPalette S J := by
  by_cases hZero : J = ⊥
  · subst J
    rw [originalEquivDiversityPalette_bot S] at hInside
    obtain ⟨a,ha⟩ := hAB
    exact False.elim (Set.not_mem_empty a (hInside ha))
  · have hJ : (⊥ : ColourEq S i) < J :=
      lt_of_le_of_ne bot_le hZero.symm
    have hK : (⊥ : ColourEq S i) < K :=
      lt_of_lt_of_le hJ hJK.1.le
    obtain ⟨wJ,hwJ⟩ :=
      original_nonzero_equiv_positive_word_of_terminalNR2
        S H sap nr2 J hJ
    obtain ⟨wK,hwK⟩ :=
      original_nonzero_equiv_positive_word_of_terminalNR2
        S H sap nr2 K hK
    have hExactA : StrongExact.Exact S A :=
      (original_typed_PC_fixed_domain_iff_exact S H sap cco A).mp hA
    have hExactB : StrongExact.Exact S B :=
      (original_typed_PC_fixed_domain_iff_exact S H sap cco B).mp hB
    exact original_full_MI_strong_exact_prime
      S H sap cco J K hMI hJK hJ wJ wK hwJ hwK
        A B hExactA hExactB hAB hInside

end CCO.TransitionClosure
