import CCO.TerminalLattice.RealizedNetworkReset
import Mathlib.Data.Fintype.Basic

/-!
# B050 C31: finite OLD fine-atom indexing of complete external quotient orbitals

The original old G-action and old pair homogeneity, not the automorphism
group of a quotient reduct, make each complete quotient orbital determined
by its representing OLD fine pair colour.

The finite indexing set consists of actual OLD diversity colours which
occur on pairs K-related but not J-related.  Indexing by these fine
colours may list the same complete quotient orbital more than once,
which is harmless for the source sparse-labelled graph and does not
assume a fictitious quotient action or change the theorem contract.
Every external complete OLD G-orbital is represented.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- C31 literal ORIGINAL full-group quotient orbital equality:
two pairs of REAL points with the same fine old pair colour determine
exactly the same complete quotient G-orbital. This is not homogeneity
of an independently constructed quotient structure. -/
theorem originalQuotientOrbitalPalette_eq_of_fine_colour
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (a b x y : X i)
    (hColour : S.colour a b = S.colour x y) :
    originalQuotientOrbitalPalette S (G := G) J a b =
      originalQuotientOrbitalPalette S (G := G) J x y := by
  obtain ⟨g, hga, hgb⟩ :=
    S.pair_homogeneous_of_homogeneous H a x b y hColour
  have hOrb : originalQuotientOrbital S (G := G) J a b =
      originalQuotientOrbital S (G := G) J x y := by
    funext q r
    apply propext
    constructor
    · rintro ⟨k, hkq, hkr⟩
      refine ⟨k * g⁻¹, ?_, ?_⟩
      · change Quotient.mk J.val ((k * g⁻¹) • x) = q
        rw [mul_smul, ← hga, inv_smul_smul]
        exact hkq
      · change Quotient.mk J.val ((k * g⁻¹) • y) = r
        rw [mul_smul, ← hgb, inv_smul_smul]
        exact hkr
    · rintro ⟨k, hkq, hkr⟩
      refine ⟨k * g, ?_, ?_⟩
      · change Quotient.mk J.val ((k * g) • a) = q
        rw [mul_smul, hga]
        exact hkq
      · change Quotient.mk J.val ((k * g) • b) = r
        rw [mul_smul, hgb]
        exact hkr
  simp only [originalQuotientOrbitalPalette, hOrb]

/-- EXACT finite indices: a colour qualifies iff it actually appears
on some pair in the full original upper K-equivalence but outside J.
This is a subtype of the existing finite OLD fine-atom palette. -/
abbrev OriginalExternalAtom {i : ι}
    (J K : ColourEq S i) :=
  {c : S.Atom i i //
    ∃ x y : X i, K x y ∧ ¬ J x y ∧ S.colour x y = some c}

noncomputable instance originalExternalAtom_fintype {i : ι}
    (J K : ColourEq S i) :
    Fintype (OriginalExternalAtom S J K) := by
  letI : Fintype (S.Atom i i) := S.finiteAtom i i
  exact Fintype.ofFinite _

private theorem originalExternalAtom_has_pair {i : ι}
    (J K : ColourEq S i) (c : OriginalExternalAtom S J K) :
    ∃ p : X i × X i,
      K p.1 p.2 ∧ ¬ J p.1 p.2 ∧
        S.colour p.1 p.2 = some c.val := by
  obtain ⟨x,y,hK,hNotJ,hCol⟩ := c.property
  exact ⟨(x,y),hK,hNotJ,hCol⟩

/-- A chosen ACTUAL real pair realizing one qualifying old fine
colour. Only allowed Classical.choice selects a representative;
all listed relations remain those of the full original old G-action. -/
noncomputable def originalExternalAtomWitness {i : ι}
    (J K : ColourEq S i) (c : OriginalExternalAtom S J K) :
    {p : X i × X i //
      K p.1 p.2 ∧ ¬ J p.1 p.2 ∧
        S.colour p.1 p.2 = some c.val} :=
  ⟨Classical.choose (originalExternalAtom_has_pair S J K c),
    Classical.choose_spec (originalExternalAtom_has_pair S J K c)⟩

/-- Fixed finite family, indexed by Fin of ACTUAL qualifying old
diversity atoms. It may contain repeated COMPLETE orbitals but no
fine subset or quotient-group enlargement. -/
noncomputable def originalIndexedExternalOrbitalMenus {i : ι}
    (J K : ColourEq S i) :
    Fin (Fintype.card (OriginalExternalAtom S J K)) → S.Menu i i :=
  fun j =>
    let c : OriginalExternalAtom S J K :=
      (Fintype.equivFin (OriginalExternalAtom S J K)).symm j
    let p := (originalExternalAtomWitness S J K c).val
    originalQuotientOrbitalPalette S (G := G) J p.1 p.2

/-- C31 finite cover: EVERY original K-external real pair has its
literal COMPLETE original-G quotient orbital in the fixed family.
No quotient homogeneity, SAP, CCO, NR2 or already-proved reset
is needed; equality follows from old homogeneous pair colours. -/
theorem originalIndexedExternalOrbitalMenus_cover
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i)
    (x y : X i) (hKxy : K x y) (hNotJ : ¬ J x y) :
    ∃ j : Fin (Fintype.card (OriginalExternalAtom S J K)),
      originalIndexedExternalOrbitalMenus S (G := G) J K j =
        originalQuotientOrbitalPalette S (G := G) J x y := by
  have hxy : x ≠ y := by
    intro heq
    subst y
    exact hNotJ (J.val.refl x)
  have hTag : (⟨i,x⟩ : Sigma X) ≠ ⟨i,y⟩ := by
    intro heq
    have h : x = y := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
    exact hxy h
  obtain ⟨a, hColour⟩ := S.some_colour_of_ne x y hTag
  let c : OriginalExternalAtom S J K :=
    ⟨a, ⟨x,y,hKxy,hNotJ,hColour⟩⟩
  let p := originalExternalAtomWitness S J K c
  have hOldColour : S.colour p.val.1 p.val.2 =
      S.colour x y := p.property.2.2.trans hColour.symm
  have hOrbital : originalQuotientOrbitalPalette S (G := G) J
      p.val.1 p.val.2 =
        originalQuotientOrbitalPalette S (G := G) J x y :=
    originalQuotientOrbitalPalette_eq_of_fine_colour
      S H J p.val.1 p.val.2 x y hOldColour
  refine ⟨(Fintype.equivFin (OriginalExternalAtom S J K)) c, ?_⟩
  simpa only [originalIndexedExternalOrbitalMenus,
    Equiv.symm_apply_apply] using hOrbital


/-- The C31 fixed finite list has ONLY actual nonempty complete old-G
external orbitals. Each menu lies inside K-diversity and is disjoint
from J-diversity. Neither full-cover powers nor original CCO is used;
a mere J≤K suffices for this well-typed OLD G family. -/
theorem originalIndexedExternalOrbitalMenus_valid
    (H : HomogeneousSource S G) {i : ι}
    (J K : ColourEq S i) (hJK : J ≤ K) :
    ∀ j : Fin (Fintype.card (OriginalExternalAtom S J K)),
      (originalIndexedExternalOrbitalMenus S (G := G) J K j).Nonempty ∧
      originalIndexedExternalOrbitalMenus S (G := G) J K j ⊆
        originalEquivDiversityPalette S K ∧
      (∀ c ∈ originalIndexedExternalOrbitalMenus S (G := G) J K j,
        c ∉ originalEquivDiversityPalette S J) := by
  intro j
  let c : OriginalExternalAtom S J K :=
    (Fintype.equivFin (OriginalExternalAtom S J K)).symm j
  let p := originalExternalAtomWitness S J K c
  have hKpq : K p.val.1 p.val.2 := p.property.1
  have hNotJpq : ¬ J p.val.1 p.val.2 := p.property.2.1
  have hpne : p.val.1 ≠ p.val.2 := by
    intro heq
    exact hNotJpq (heq ▸ J.val.refl p.val.1)
  have hTag : (⟨i,p.val.1⟩ : Sigma X) ≠ ⟨i,p.val.2⟩ := by
    intro heq
    have hh : p.val.1 = p.val.2 := by
      simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using heq
    exact hpne hh
  obtain ⟨d, hCol⟩ := S.some_colour_of_ne p.val.1 p.val.2 hTag
  have hRoot : d ∈ originalQuotientOrbitalPalette S (G := G)
      J p.val.1 p.val.2 :=
    ⟨p.val.1, p.val.2,
      ⟨hpne, originalQuotientOrbital_root S (G := G) J p.val.1 p.val.2⟩, hCol⟩
  change (originalQuotientOrbitalPalette S (G := G) J
    p.val.1 p.val.2).Nonempty ∧
    originalQuotientOrbitalPalette S (G := G) J p.val.1 p.val.2 ⊆
      originalEquivDiversityPalette S K ∧
    (∀ a ∈ originalQuotientOrbitalPalette S (G := G) J p.val.1 p.val.2,
      a ∉ originalEquivDiversityPalette S J)
  refine ⟨⟨d,hRoot⟩, ?_, ?_⟩
  · exact original_full_external_orbital_inside_K
      S H J K hJK p.val.1 p.val.2 hKpq
  · intro a ha haJ
    obtain ⟨u,v,hJuv,hColUV⟩ := haJ
    obtain ⟨x,y,⟨_,hOrbXY⟩,hColXY⟩ := ha
    have hJxy : J x y :=
      (J.property u v x y (hColUV.trans hColXY.symm)).mp hJuv
    have hQ : Quotient.mk J.val x = Quotient.mk J.val y :=
      Quotient.sound hJxy
    rw [← hQ] at hOrbXY
    exact (originalQuotientOrbital_irreflexive
      S H J p.val.1 p.val.2 hNotJpq
      (Quotient.mk J.val x)) hOrbXY


end CCO.TerminalLattice
