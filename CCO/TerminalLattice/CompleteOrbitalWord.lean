import CCO.TerminalLattice.SameJAtomSaturation
import CCO.PositiveWords

/-!
# B050 C22–C23: complete OLD quotient orbital = J-diversity saturation
of ONE actual fine diversity atom, hence one genuinely positive word.

No B049 module is imported, and no assertion that a fine atom itself is
J-bisaturated is made. In contrast, its full OLD quotient G-orbital
pullback is precisely the J;t;J diversity guard, shown directly using
the original ambient group pair-homogeneity. The C21 SAP proof then
upgrades RAW external J steps to genuine OLD STRONG diversity steps.
-/

universe u v w t
namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- C22, preliminary RAW identity: the COMPLETE quotient orbital
through the actual OLD fine atom t is exactly the diversity slice of
the OLD RAW J;t;J relation. Quotient equality never becomes an OLD
STRONG identity, and the ambient group is the original one. -/
theorem originalQuotientOrbital_raw_J_atom_J
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (tAtom : S.Atom i i)
    (p q : X i) (hpq : S.atomRel tAtom p q) :
    originalQuotientOrbitalPalette S (G := G) J p q =
      S.diversityGuard (originalRawJSandwich S J tAtom) := by
  classical
  apply Set.Subset.antisymm
  · rintro c ⟨x,z,⟨hxzNe,⟨g,hgP,hgQ⟩⟩,hcol⟩
    have hJx : J x (g • p) :=
      J.val.symm (Quotient.exact hgP)
    have hJz : J (g • q) z := Quotient.exact hgQ
    have hAtom : S.atomRel tAtom (g • p) (g • q) := by
      change S.colour (g • p) (g • q) = some tAtom
      exact (S.colourInvariant_of_homogeneous H g p q).trans hpq
    exact ⟨x,z,⟨g • p,g • q,hJx,hAtom,hJz⟩,hcol⟩
  · rintro c ⟨x,z,⟨u,v,hJxu,hUV,hJvz⟩,hcol⟩
    obtain ⟨g,hgP,hgQ⟩ :=
      S.pair_homogeneous_of_homogeneous H
        p u q v (hpq.trans hUV.symm)
    have hOrbP : Quotient.mk J.val (g • p) = Quotient.mk J.val x := by
      rw [hgP]
      exact (Quotient.sound hJxu).symm
    have hOrbQ : Quotient.mk J.val (g • q) = Quotient.mk J.val z := by
      rw [hgQ]
      exact Quotient.sound hJvz
    have hxzNe : x ≠ z := by
      intro h
      exact S.atomRel_ne hcol (congrArg (Sigma.mk i) h)
    exact ⟨x,z,⟨hxzNe,⟨g,hOrbP,hOrbQ⟩⟩,hcol⟩

/-- C22, FULL original STRONG version:
  T_{[p],[q]} = J^circ star {t} star J^circ.
This is a complete quotient orbital, not a fine unsaturated packet.
The original SAP premise is consumed only by C21's fresh OLD
intermediate representatives; there is NO cover or CCO hypothesis. -/
theorem originalQuotientOrbital_strong_J_atom_J
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (tAtom : S.Atom i i)
    (p q : X i) (hpq : S.atomRel tAtom p q) :
    originalQuotientOrbitalPalette S (G := G) J p q =
      S.product (originalEquivDiversityPalette S J)
        (S.product ({tAtom} : S.Menu i i)
          (originalEquivDiversityPalette S J)) := by
  calc
    originalQuotientOrbitalPalette S (G := G) J p q =
        S.diversityGuard (originalRawJSandwich S J tAtom) :=
      originalQuotientOrbital_raw_J_atom_J S H J tAtom p q hpq
    _ = _ := original_raw_J_atom_J_guard_eq_strong S H sap J hJ tAtom

/-- SOURCE C23: if the old nontrivial J-diversity palette has ONE
genuinely POSITIVE original atomic word, then EVERY complete OLD
quotient G-orbital through a fine atom t has ONE positive word.
No K-diversity word, exactness, NR2, global CCO or B049 saturation
is presumed. The same J-word is reused on both sides. -/
theorem originalQuotientOrbital_positive_word
    (H : HomogeneousSource S G) (sap : AgeSAP S) {i : ι}
    (J : ColourEq S i) (hJ : (⊥ : ColourEq S i) < J)
    (wJ : PositiveWord S i i)
    (hwJ : PositiveWord.profile S wJ =
      originalEquivDiversityPalette S J)
    (tAtom : S.Atom i i)
    (p q : X i) (hpq : S.atomRel tAtom p q) :
    ∃ word : PositiveWord S i i,
      PositiveWord.profile S word =
        originalQuotientOrbitalPalette S (G := G) J p q := by
  let w : PositiveWord S i i :=
    PositiveWord.append S wJ
      (PositiveWord.append S (.single tAtom) wJ)
  refine ⟨w, ?_⟩
  calc
    PositiveWord.profile S w =
        S.product (PositiveWord.profile S wJ)
          (PositiveWord.profile S
            (PositiveWord.append S (.single tAtom) wJ)) :=
      PositiveWord.profile_append_of_SAP S H sap wJ
        (PositiveWord.append S (.single tAtom) wJ)
    _ = S.product (originalEquivDiversityPalette S J)
          (S.product ({tAtom} : S.Menu i i)
            (originalEquivDiversityPalette S J)) := by
      rw [PositiveWord.profile_append_of_SAP S H sap, hwJ]
      rfl
    _ = originalQuotientOrbitalPalette S (G := G) J p q :=
      (originalQuotientOrbital_strong_J_atom_J S H sap
        J hJ tAtom p q hpq).symm

end CCO.TerminalLattice
