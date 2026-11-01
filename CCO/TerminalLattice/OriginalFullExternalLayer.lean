import CCO.TerminalLattice.OriginalQuotientExternalLayerSemantics
import CCO.TerminalLattice.OriginalKPositiveFromExternal
import CCO.TerminalLattice.SingletonExternalLayer
import CCO.TerminalLattice.FullCoverIndexTwo

/-!
# B050 source09 OWL: unconditional positive OLD word for the full external layer

This is precisely the final source09 `thm:typed-original-full-cover-layer-word`
with its original hypotheses: an ORIGINAL full invariant cover Id < J ⋖ K,
original homogeneous SAP and semantic CCO, and one positive OLD typed word
for J-diversity. There is NO positive-K-word assumption, no NR2,
quotient-reduct automorphism group, quotient SAP/CCO, or exactness premise.

Choose one actual external pair. At relative index two, the accepted
full-cover theorem makes its complete original-G quotient orbital the ENTIRE
external layer, and the earlier singleton-old-word theorem applies.

Otherwise, the proven CCO-free full-cover powers first CONSTRUCT a positive
OLD word for K-diversity. The already proved unconditional original
one-network reset supplies a COMPLETE original-G external orbital M0 with
quotient square K/J. If there is only one external complete orbital, use
the singleton-old-word case. If another exists, the fully formalized
original positive-state Helly/finite escape/periodicity argument refutes
the assumption that every distinct mixed orbital product avoids the full
external layer. Hence some genuine distinct complete orbitals have quotient
product exactly (K/J) minus the TRUE J-quotient diagonal; concatenate their
actual positive OLD words, using the proved SAP quotient-semigroup identity.

This discharges the source09 finite-escape theorem without assuming a
hypothetical positive external layer, finite quotient carrier, fabricated
identity factor, or already existing mixed orbital pair.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- SOURCE09 OWL: from one real old positive word of J-diversity,
construct ONE positive original typed diversity word presenting the
WHOLE external K-minus-J STRONG fine-atom menu.

The hypotheses are EXACTLY original homogeneity, original SAP, original
homomorphic CCO, a nonzero FULL original cover and the given old J-word.
In particular the relative index TWO case is included and K-positivity
is a DERIVED statement in the multiple-orbital branch. -/
theorem original_full_cover_external_layer_positive_word
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    (cco : SemanticCCO.{u,v,max u v,w} S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ⋖ K) (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J) :
    ∃ word : PositiveWord S i i,
      PositiveWord.profile S word =
        originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J := by
  classical
  have hNotKJ : ¬ K ≤ J := not_le_of_gt hJK.lt
  have hExternal : ∃ a b : X i, K a b ∧ ¬ J a b := by
    by_contra hNone
    apply hNotKJ
    intro a b hab
    by_contra hne
    exact hNone ⟨a,b,hab,hne⟩
  obtain ⟨a,b,hab,hne⟩ := hExternal
  by_cases hTwo : relativeIndex J.val K.val a = 2
  · have hBase :
        originalQuotientOrbital S (G := G) J a b =
          originalQuotientExternalLayer S J K hJK.le :=
      originalQuotientOrbital_index_two_external
        S H J K hJK a b hab hne hTwo
    have hUnique :
        ∀ x y : X i, K x y → ¬ J x y →
          originalQuotientOrbitalPalette S (G := G) J x y =
            originalQuotientOrbitalPalette S (G := G) J a b := by
      intro x y hKxy hNotJxy
      have hRoot :
          originalQuotientOrbital S (G := G) J a b
            (Quotient.mk J.val x) (Quotient.mk J.val y) := by
        rw [hBase]
        exact ⟨(originalUpperSetoid_mk S J K hJK.le x y).mpr hKxy,
          fun hEq => hNotJxy (Quotient.exact hEq)⟩
      have hOrbEq :
          originalQuotientOrbital S (G := G) J x y =
            originalQuotientOrbital S (G := G) J a b :=
        originalQuotientOrbital_eq_of_overlap
          S H J x y a b
            (Quotient.mk J.val x) (Quotient.mk J.val y)
            (originalQuotientOrbital_root S (G := G) J x y) hRoot
      unfold originalQuotientOrbitalPalette
      rw [hOrbEq]
    exact original_singleton_external_layer_positive_word
      S H sap J K hJK.le hJ wJ hwJ a b hab hne hUnique
  · obtain ⟨p,z,hKpz,hNotJpz,hReset⟩ :=
      original_full_cover_quotient_reset_of_Jpositive
        S H sap cco J K hJK hJ a hTwo wJ hwJ
    by_cases hDifferent :
        ∃ c d : X i, K c d ∧ ¬ J c d ∧
          originalQuotientOrbital S (G := G) J c d ≠
            originalQuotientOrbital S (G := G) J p z
    · have hMixedExists :
          ∃ c d : X i, K c d ∧ ¬ J c d ∧
            originalQuotientOrbital S (G := G) J c d ≠
              originalQuotientOrbital S (G := G) J p z ∧
            RawSymmetric.compose
              (originalQuotientOrbital S (G := G) J p z)
              (originalQuotientOrbital S (G := G) J c d) =
              originalQuotientExternalLayer S J K hJK.le := by
        by_contra hAbsent
        have hNoMixed :
            ∀ c d : X i, K c d → ¬ J c d →
              originalQuotientOrbital S (G := G) J c d ≠
                originalQuotientOrbital S (G := G) J p z →
              RawSymmetric.compose
                (originalQuotientOrbital S (G := G) J p z)
                (originalQuotientOrbital S (G := G) J c d) ≠
                originalQuotientExternalLayer S J K hJK.le := by
          intro c d hKcd hNotJcd hNE hEq
          exact hAbsent ⟨c,d,hKcd,hNotJcd,hNE,hEq⟩
        exact original_no_mixed_full_impossible_of_different
          S H sap cco J K hJK hJ a hTwo wJ hwJ
            p z hKpz hNotJpz hReset hDifferent hNoMixed
      obtain ⟨c,d,hKcd,hNotJcd,_,hMixed⟩ := hMixedExists
      exact original_external_layer_word_of_mixed_orbitals
        S H sap J K hJK.le hJ wJ hwJ
          p z c d hKpz hNotJpz hKcd hNotJcd hMixed
    · have hUnique :
          ∀ x y : X i, K x y → ¬ J x y →
            originalQuotientOrbitalPalette S (G := G) J x y =
              originalQuotientOrbitalPalette S (G := G) J p z := by
        intro x y hKxy hNotJxy
        have hOrbEq :
            originalQuotientOrbital S (G := G) J x y =
              originalQuotientOrbital S (G := G) J p z := by
          by_contra hNE
          exact hDifferent ⟨x,y,hKxy,hNotJxy,hNE⟩
        unfold originalQuotientOrbitalPalette
        rw [hOrbEq]
      exact original_singleton_external_layer_positive_word
        S H sap J K hJK.le hJ wJ hwJ p z hKpz hNotJpz hUnique

end CCO.TerminalLattice
