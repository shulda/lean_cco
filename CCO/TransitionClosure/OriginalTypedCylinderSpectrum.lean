import CCO.TransitionClosure.TypedRawStrongSaturation
import CCO.TransitionClosure.TypedIdentityExterior

/-!
# B049 source07 C41-C43: actual typed original representative cylinder

A pair of ACTUAL old quotient classes q in X_i/J and r in X_j/K
has one complete OLD diversity-fine representative spectrum:
all source fine atoms carried by pairs of distinct real
representatives in those classes. This is not a chosen
fine suborbital and does not invent a hidden quotient action.

If an actual original atom a links one pair of representatives,
the entire cylinder spectrum equals the diversity part of
the genuine RAW typed J;{a};K relation. The inclusion from
an arbitrary RAW witness uses a SINGLE original group motion
aligning the complete old middle a-pair to the fixed real
representatives. Original named sorts may differ.

In particular if two such class-pair spectra have ONE common
old fine atom then the FULL spectra are identical, supplying
the complete-orbital partition property needed before hidden
binary type naming.

No SAP/CCO, quotient SAP/CCO, NR2, fictional identity atom,
or real-to-hidden definability assumption enters these
RAW representative-spectrum identities.
-/

universe u v w t

namespace CCO.TransitionClosure

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ s : ι, MulAction G (X s)]

open ParityHasse.Original

/-- The precise FULL old diversity representative spectrum of
an ACTUAL pair of J,K quotient classes on possibly DIFFERENT
original named sorts. Hidden same-sort quotient equality is
a separate logical test, not an OLD diversity fine atom. -/
def originalTypedQuotientPairSpectrum
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (q : Quotient J.val) (r : Quotient K.val) :
    S.Menu i j :=
  {c | ∃ x : X i, ∃ y : X j,
    Quotient.mk J.val x = q ∧ Quotient.mk K.val y = r ∧
    S.atomRel c x y}

/-- SOURCE07 C41 literal REAL cylinder identity. Whenever one old
fine a-pair links q,r, the entire fine representative spectrum
is the diversity guard of ORIGINAL RAW J;{a};K, including its
true identity-allowed outer steps.

The proof of the reverse direction aligns the actual old
middle a-pair by original COMPLETE pair homogeneity, while
preserving the original exterior J/K classes. There is no
extra quotient homogeneity or arbitrary choice of section. -/
theorem originalTypedQuotientPairSpectrum_eq_raw
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (a : S.Atom i j) (x : X i) (y : X j)
    (hxy : S.atomRel a x y) :
    originalTypedQuotientPairSpectrum S J K
        (Quotient.mk J.val x) (Quotient.mk K.val y) =
      S.diversityGuard (originalRawTypedSandwich S J K a) := by
  ext c
  constructor
  · rintro ⟨x',y',hq,hr,hcol⟩
    have hJ : J x' x := Quotient.exact hq
    have hK : K y y' := K.val.symm (Quotient.exact hr)
    exact ⟨x',y',⟨x,y,hJ,hxy,hK⟩,hcol⟩
  · rintro ⟨x',y',⟨u,v,hJxu,hAtom,hKvy⟩,hCol⟩
    obtain ⟨g,hgu,hgv⟩ :=
      S.pair_homogeneous_of_homogeneous H u x v y
        (hAtom.trans hxy.symm)
    have hJg : J (g • x') x := by
      have hMove :=
        colourInvariant_groupInvariant S H J.property g x' u hJxu
      simpa only [hgu] using hMove
    have hKg : K y (g • y') := by
      have hMove :=
        colourInvariant_groupInvariant S H K.property g v y' hKvy
      simpa only [hgv] using hMove
    have hColg : S.atomRel c (g • x') (g • y') :=
      (S.colourInvariant_of_homogeneous H g x' y').trans hCol
    exact ⟨g • x',g • y',
      Quotient.sound hJg,
      Quotient.sound (K.val.symm hKg),
      hColg⟩

/-- C43 old fine spectrum uniqueness: if two literal typed
quotient class-pairs have an ACTUAL common diversity fine atom,
their FULL original representative spectra are the same.
No hidden binary partition or unrelated quotient orbital is
postulated: this is proved by source pair-homogeneity. -/
theorem originalTypedQuotientPairSpectrum_eq_of_overlap
    (H : HomogeneousSource S G)
    {i j : ι} (J : ColourEq S i) (K : ColourEq S j)
    (q q' : Quotient J.val) (r r' : Quotient K.val)
    (hOverlap : (originalTypedQuotientPairSpectrum S J K q r ∩
      originalTypedQuotientPairSpectrum S J K q' r').Nonempty) :
    originalTypedQuotientPairSpectrum S J K q r =
      originalTypedQuotientPairSpectrum S J K q' r' := by
  obtain ⟨c,hLeft,hRight⟩ := hOverlap
  obtain ⟨x,y,hqx,hry,hxy⟩ := hLeft
  obtain ⟨x',y',hqx',hry',hxy'⟩ := hRight
  calc
    originalTypedQuotientPairSpectrum S J K q r =
        originalTypedQuotientPairSpectrum S J K
          (Quotient.mk J.val x) (Quotient.mk K.val y) := by
            rw [hqx,hry]
    _ = S.diversityGuard (originalRawTypedSandwich S J K c) :=
      originalTypedQuotientPairSpectrum_eq_raw S H J K c x y hxy
    _ = originalTypedQuotientPairSpectrum S J K
          (Quotient.mk J.val x') (Quotient.mk K.val y') :=
      (originalTypedQuotientPairSpectrum_eq_raw
        S H J K c x' y' hxy').symm
    _ = originalTypedQuotientPairSpectrum S J K q' r' := by
      rw [hqx',hry']

end CCO.TransitionClosure
