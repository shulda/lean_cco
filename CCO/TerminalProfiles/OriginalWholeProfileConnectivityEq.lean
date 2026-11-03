import CCO.TerminalProfiles.OriginalWholeProfileStabilization
import CCO.TerminalProfiles.OriginalEquivalenceReproduction
import CCO.ParityHasse.Original.ParitySeed
import CCO.TerminalLattice.FibreSAP

/-!
# B051 TWP: the stabilized original FULL connectivity equivalence

Finite positive OLD whole-word walks, with the source's real zero-length
diagonal, define an original full colour-invariant equivalence. Since
the word's STRONG old profile is genuinely nonempty by visible SAP,
the equivalence is strictly above logical equality. Its diversity
palette is exactly the all-length connectedness palette in source09.

The eventually stable STRONG old word profile is thus positive reachable
and idempotent by the separately compiled original equivalence
reproduction theorem TER. No quotient SAP/CCO or artificial identity.
-/

universe u v w t

namespace CCO.TerminalProfiles

open CCO.ParityHasse.Original
open CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Genuine ORIGINAL invariant old-walk connectedness, not a
hypothetical quotient automorphism relation or exact sublattice. -/
noncomputable def originalWholeProfileConnectivityEq
    (H : HomogeneousSource S G)
    {i : ι} (word : PositiveWord S i i) : ColourEq S i := by
  let R : X i → X i → Prop := PositiveWord.represented S word
  have hInv : TRel.Invariant (G := G) R :=
    PositiveWord.represented_invariant_of_homogeneous S H word
  have hColour : ColourInvariant S i R :=
    groupInvariant_colourInvariant S H hInv
  have hSymm : ∀ x y, R x y → R y x :=
    colourInvariant_symmetric S hColour
  refine ⟨connectivitySetoid R hSymm, ?_⟩
  intro x y x' y' hcol
  constructor
  · rintro ⟨n,hxy⟩
    exact ⟨n,
      (colourInvariant_relPow S H hColour n x y x' y' hcol).mp hxy⟩
  · rintro ⟨n,hxy⟩
    exact ⟨n,
      (colourInvariant_relPow S H hColour n x y x' y' hcol).mpr hxy⟩

/-- This is a literal equality of the original OLD diversity palette
of that FULL invariant connectivity equivalence. -/
theorem originalWholeProfileConnectedPalette_eq_diversity
    (H : HomogeneousSource S G)
    {i : ι} (word : PositiveWord S i i) :
    originalWholeProfileConnectedPalette S word =
      originalEquivDiversityPalette S
        (originalWholeProfileConnectivityEq S H word) := by
  rfl

/-- Every real positive OLD typed word has a nontrivial ORIGINAL
connectedness equivalence; there are genuine distinct old points,
rather than a positive-word name for the logical identity. -/
theorem originalWholeProfileConnectivityEq_nonzero
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (word : PositiveWord S i i) :
    (⊥ : ColourEq S i) <
      originalWholeProfileConnectivityEq S H word := by
  let J := originalWholeProfileConnectivityEq S H word
  obtain ⟨a,ha⟩ := PositiveWord.profile_nonempty_of_SAP S H sap word
  have hGuard := PositiveWord.diversityGuard_represented_eq_profile_of_SAP
    S H sap word
  have haR : a ∈ S.diversityGuard (PositiveWord.represented S word) := by
    rw [hGuard]
    exact ha
  obtain ⟨x,y,hRxy,hcol⟩ := haR
  have hne : x ≠ y := by
    intro h
    exact S.atomRel_ne hcol (congrArg (Sigma.mk i) h)
  have hJxy : J x y := by
    change ConnectedWalk (PositiveWord.represented S word) x y
    exact ⟨1,(relPow_one _ x y).mpr hRxy⟩
  have hNot : (⊥ : ColourEq S i) ≠ J := by
    intro heq
    have hEq : x = y := by
      have hb : (⊥ : ColourEq S i) x y := by
        rw [heq]
        exact hJxy
      exact hb
    exact hne hEq
  exact lt_of_le_of_ne bot_le hNot

/-- SOURCE09 TWP: the stabilized same-sort profile is the diversity
palette of an ACTUAL nontrivial ORIGINAL full invariant equivalence;
it is itself ONE reachable positive typed word and STRONG idempotent.
The uniform power threshold is for every later exponent n+1. -/
theorem original_terminal_whole_profile_pure_power
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (nr2 : CCO.Selectors.OriginalNR2 S)
    {i : ι} (word : PositiveWord S i i) :
    ∃ J : ColourEq S i, (⊥ : ColourEq S i) < J ∧
      ∃ N : Nat, 0 < N ∧
        (∀ n, N ≤ n →
          originalStrongPalettePower S (PositiveWord.profile S word) n =
            originalEquivDiversityPalette S J) ∧
        S.product (originalEquivDiversityPalette S J)
            (originalEquivDiversityPalette S J) =
          originalEquivDiversityPalette S J ∧
        ∃ laterWord : PositiveWord S i i,
          PositiveWord.profile S laterWord =
            originalEquivDiversityPalette S J := by
  let J := originalWholeProfileConnectivityEq S H word
  have hJ : (⊥ : ColourEq S i) < J :=
    originalWholeProfileConnectivityEq_nonzero S H sap word
  obtain ⟨N,hN,hStable⟩ :=
    original_whole_positive_profile_powers_stabilize S H sap nr2 word
  have hE : (originalEquivDiversityPalette S J).Nonempty := by
    obtain ⟨x,y,hxy,hne⟩ := actual_nontrivial_equiv_pair S J hJ
    cases hc : S.colour x y with
    | none =>
        have hh : x = y := by
          have ht := (S.colour_none_iff x y).mp hc
          simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using ht
        exact False.elim (hne hh)
    | some a =>
        exact ⟨a,x,y,hxy,hc⟩
  have hIdem :
      S.product (originalEquivDiversityPalette S J)
          (originalEquivDiversityPalette S J) =
        originalEquivDiversityPalette S J :=
    (original_equiv_diversity_reproduction S H sap J hJ
      (originalEquivDiversityPalette S J) hE
      (by intro a ha; exact ha)).2.2
  refine ⟨J,hJ,N,hN,?_,hIdem,?_⟩
  · intro n hn
    exact (hStable n hn).trans
      (originalWholeProfileConnectedPalette_eq_diversity S H word)
  · refine ⟨originalRepeatedPositiveWord S word N, ?_⟩
    calc
      PositiveWord.profile S (originalRepeatedPositiveWord S word N) =
        originalStrongPalettePower S (PositiveWord.profile S word) N :=
          originalRepeatedPositiveWord_profile S H sap word N
      _ = originalEquivDiversityPalette S J :=
        (hStable N le_rfl).trans
          (originalWholeProfileConnectedPalette_eq_diversity S H word)

end CCO.TerminalProfiles
