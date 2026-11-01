import CCO.TerminalLattice.OriginalFullCoverReset
import CCO.TerminalLattice.TerminalExactCover
import CCO.PositiveWords

/-!
# B050 C41: full ORIGINAL terminal reset from the proved C40 source instance

Under the full ORIGINAL sortwise NR2 hypothesis, accepted B011 gives
a true equality-inclusive RAW atomic word for every full invariant
equivalence. For nonzero E, this word cannot represent only logical
identity. Normalizing its actual OLD RAW atomic letters therefore
produces one genuinely POSITIVE typed original diversity word. The
source's real AgeSAP turns the word's diversity guard into its exact
original STRONG endpoint profile E°.

The terminal exact-to-FULL order isomorphism of B011 lifts a genuine
cover in the represented exact lattice to a FULL original cover.
Original NR2 rules out local index two at a real old anchor. Both
positive presentations are now SOURCE DERIVATIONS rather than new
hypotheses, so the just-proved one-global-CCO C40 reset applies.

No quotient SAP, B049 provider, invented positive identity word,
extra reset hypothesis, or new CCO call is introduced here.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Original terminal RAW one-word existence, plus genuine old
AgeSAP, proves a POSITIVE OLD word for each NONZERO full original
invariant equivalence E. The RAW identity-only case is ruled out
using E>Id; we never treat old equality as a STRONG factor.

Other named original sorts can appear inside this positive word;
only its endpoints belong to the fixed old sort i.
No SemanticCCO is used to produce the word. -/
theorem original_terminal_nonzero_positive_word
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (nr2 : RealClosure.Bounds.SortNR2 S i)
    (E : ColourEq S i)
    (hE : (⊥ : ColourEq S i) < E) :
    ∃ word : PositiveWord S i i,
      PositiveWord.profile S word =
        originalEquivDiversityPalette S E := by
  obtain ⟨raw,hRaw⟩ :=
    RealClosure.Bounds.terminal_one_raw_word S H nr2 E
  rcases PositiveWord.raw_relation_identity_or_positive S raw with
    ⟨_,hIdent⟩ | ⟨word,hPositive⟩
  · have hEbot : E ≤ (⊥ : ColourEq S i) := by
      intro x y hxy
      have hOld : RawWord.relation S raw x y := by
        rw [hRaw]
        exact hxy
      have htag := (hIdent x y).mp hOld
      change x = y
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using htag
    exact False.elim ((not_le_of_gt hE) hEbot)
  · refine ⟨word, ?_⟩
    calc
      PositiveWord.profile S word =
          S.diversityGuard (PositiveWord.represented S word) :=
        (PositiveWord.diversityGuard_represented_eq_profile_of_SAP
          S H sap word).symm
      _ = originalEquivDiversityPalette S E := by
        rw [← hPositive, hRaw]
        rfl

/-- SOURCE C41 `thm:typed-relative-reset` in its exact terminal
represented-cover formulation. J,K are actual original exact
equivalences, and the proof obtains their corresponding FULL original
invariant cover and BOTH positive old word profiles. Under the
standing original sortwise NR2, the local index-two exception is
discharged at an actual source point, then C40 supplies one complete
original ambient-G quotient orbital m with BOTH squares:
  m star m = K°  (true original STRONG diversity);
  m ; m = K    (true equality-inclusive old RAW relation).

No new positive-word/cover/network premise is introduced. -/
theorem original_terminal_relative_reset
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (nr2 : RealClosure.Bounds.SortNR2 S i)
    (J K : ExactCRT.ExactEq S H cco i)
    (hJK : J ⋖ K)
    (hJ : (⊥ : ExactCRT.ExactEq S H cco i) < J) :
    let e := RealClosure.Bounds.terminalExactOrderIso S H cco nr2
    let Jf : ColourEq S i := e.symm J
    let Kf : ColourEq S i := e.symm K
    ∃ p z : X i, Kf p z ∧ ¬ Jf p z ∧
      (S.product
        (originalQuotientOrbitalPalette S (G := G) Jf p z)
        (originalQuotientOrbitalPalette S (G := G) Jf p z) =
          originalEquivDiversityPalette S Kf) ∧
      (RawSymmetric.compose
        (S.menuRel (originalQuotientOrbitalPalette S (G := G) Jf p z))
        (S.menuRel (originalQuotientOrbitalPalette S (G := G) Jf p z)) =
          Kf.val.r) := by
  let e := RealClosure.Bounds.terminalExactOrderIso S H cco nr2
  let Jf : ColourEq S i := e.symm J
  let Kf : ColourEq S i := e.symm K
  have hFull : Jf ⋖ Kf :=
    original_full_cover_of_terminal_exact_cover S H cco nr2 J K hJK
  have hNonzeroJ : (⊥ : ColourEq S i) < Jf :=
    original_nonzero_of_terminal_exact_nonzero S H cco nr2 J hJ
  have hNonzeroK : (⊥ : ColourEq S i) < Kf :=
    hNonzeroJ.trans hFull.lt
  obtain ⟨wJ,hwJ⟩ :=
    original_terminal_nonzero_positive_word
      S H sap nr2 Jf hNonzeroJ
  obtain ⟨wK,hwK⟩ :=
    original_terminal_nonzero_positive_word
      S H sap nr2 Kf hNonzeroK
  obtain ⟨anchor⟩ := S.nonemptySort i
  have hNotTwo : relativeIndex Jf.val Kf.val anchor ≠ 2 :=
    nr2 Jf Kf hFull.le anchor
  exact original_full_cover_reset_single_path
    S H sap cco Jf Kf hFull hNonzeroJ anchor hNotTwo
      wJ hwJ wK hwK

end CCO.TerminalLattice
