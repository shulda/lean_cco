import CCO.TerminalLattice.OriginalExternalWords

/-!
# B050 source09 C42: the singleton external quotient orbital is positive

If every ORIGINAL full-group K-external quotient pair belongs to the
SAME complete old G-orbital, its full old diversity preimage is exactly
K-diversity minus J-diversity. The internally proved C23 old-J
saturation theorem then supplies a SINGLE genuinely positive original
typed atomic word with exactly this whole profile.

This is the one-orbital branch of the original positive external-layer
theorem. It does NOT exclude relative index two, assume positivity of
K-diversity, use a quotient-reduct group or import B049. The
multiple-orbital finite-escape branch remains a separate source task.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

open ParityHasse.Original

/-- Source C42, original one-orbital case. The exact uniqueness
hypothesis means all actual K-external quotient pairs lie in the SAME
COMPLETE orbital of the original automorphism group G. Its whole
diversity preimage is precisely K° \\ J°, hence its previously proved
old positive word represents the entire external layer.

In particular there is no assumption that [K:J] differs from two. -/
theorem original_singleton_external_layer_positive_word
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J K : ColourEq S i)
    (hJK : J ≤ K) (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (p q : X i) (hKpq : K p q) (hNotJpq : ¬ J p q)
    (hUnique : ∀ x y : X i, K x y → ¬ J x y →
      originalQuotientOrbitalPalette S (G := G) J x y =
        originalQuotientOrbitalPalette S (G := G) J p q) :
    ∃ word : PositiveWord S i i,
      PositiveWord.profile S word =
        originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J := by
  have hOrbital :
      originalQuotientOrbitalPalette S (G := G) J p q =
        originalEquivDiversityPalette S K \
          originalEquivDiversityPalette S J := by
    apply Set.Subset.antisymm
    · intro c hc
      have hcK : c ∈ originalEquivDiversityPalette S K :=
        (original_full_external_orbital_inside_K
          S H J K hJK p q hKpq) hc
      have hcNotJ : c ∉ originalEquivDiversityPalette S J := by
        intro hcJ
        obtain ⟨u,v,hJuv,hColUV⟩ := hcJ
        obtain ⟨x,y,⟨_,hOrbXY⟩,hColXY⟩ := hc
        have hJxy : J x y :=
          (J.property u v x y (hColUV.trans hColXY.symm)).mp hJuv
        have hQ : Quotient.mk J.val x = Quotient.mk J.val y :=
          Quotient.sound hJxy
        rw [← hQ] at hOrbXY
        exact (originalQuotientOrbital_irreflexive
          S H J p q hNotJpq (Quotient.mk J.val x)) hOrbXY
      exact ⟨hcK,hcNotJ⟩
    · rintro c ⟨hcK,hcNotJ⟩
      obtain ⟨x,y,hKxy,hColXY⟩ := hcK
      have hNotJxy : ¬ J x y := by
        intro hJxy
        exact hcNotJ ⟨x,y,hJxy,hColXY⟩
      have hxy : x ≠ y := by
        intro heq
        subst y
        exact hNotJxy (J.val.refl x)
      have hcOrb : c ∈ originalQuotientOrbitalPalette S (G := G) J x y :=
        ⟨x,y,⟨hxy,originalQuotientOrbital_root S (G := G) J x y⟩,hColXY⟩
      rw [hUnique x y hKxy hNotJxy] at hcOrb
      exact hcOrb
  have hpqNe : p ≠ q := by
    intro heq
    subst q
    exact hNotJpq (J.val.refl p)
  have hpqTag : (⟨i,p⟩ : Sigma X) ≠ ⟨i,q⟩ := by
    intro heq
    have hh : p = q := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
    exact hpqNe hh
  obtain ⟨a,ha⟩ := S.some_colour_of_ne p q hpqTag
  obtain ⟨word,hWord⟩ :=
    originalQuotientOrbital_positive_word S H sap J hJ wJ hwJ a p q ha
  exact ⟨word,hWord.trans hOrbital⟩

end CCO.TerminalLattice
