import CCO.CloneTupleGeometry.PureSpectrum
import CCO.TerminalLattice.StrongPaletteBridge
import CCO.CloneSAP.Homogeneity

/-!
# B060 N05/N06: genuine diagonal hidden spectra and FULL MI diversity meet

The SAME quotient coordinate on its TRUE diagonal has diversity spectrum
J°, not a fabricated hidden equality atom. This first theorem holds for
arbitrary actual homogeneous named-sorted symmetric sources (no SAP/CCO).

For the REAL cloned source, the intersection of ALL actual proper FULL
MI diversity supports equals the singleton clone diversity atom. This
uses the already proved FULL MI quotient kernel theorem and genuine
finite source colour orbits. It does not identify STRONG and RAW products,
assert clone-stable terminality, or assume hidden class Helly.
-/

universe u v w t
namespace CCO.CloneTupleGeometry

open CCO.ParityHasse.Original
open CCO.TransitionClosure
open CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- B060 C28, SOURCE ACTUAL: on the *same* hidden quotient coordinate
and literal equality q=q, the full spectrum of distinct actual REAL
representatives equals the complete original J-diversity support.
No hidden diagonal is introduced into the STRONG diversity language. -/
theorem original_quotient_diagonal_spectrum
    (H : HomogeneousSource S G) {i : ι}
    (J : ColourEq S i) (q : Quotient J.val) :
    originalTypedQuotientPairSpectrum S J J q q =
      originalEquivDiversityPalette S J := by
  ext a
  constructor
  · rintro ⟨x,y,hx,hy,hcol⟩
    have hJ : J x y := Quotient.exact (hx.trans hy.symm)
    exact ⟨x,y,hJ,hcol⟩
  · rintro ⟨u,v,hJuv,hcol⟩
    obtain ⟨x,hx⟩ := Quotient.exists_rep q
    obtain ⟨g,hgu⟩ := S.original_sort_transitive_of_homogeneous H i u x
    have hJmove : J (g • u) (g • v) :=
      colourInvariant_groupInvariant S H J.property g u v hJuv
    have hJx : J x (g • v) := by
      simpa only [hgu] using hJmove
    have hy : Quotient.mk J.val (g • v) = q :=
      (Quotient.sound (J.val.symm hJx)).trans hx
    have hcolmove : S.colour (g • u) (g • v) = some a :=
      (S.colourInvariant_of_homogeneous H g u v).trans hcol
    have hc : S.atomRel a x (g • v) := by
      change S.colour x (g • v) = some a
      simpa only [hgu] using hcolmove
    exact ⟨x,g • v,hx,hy,hc⟩

/-- The exact named-quotient diagonal spectrum formula instantiated
at the concrete homogeneous pure clone source from B045. -/
theorem pure_clone_quotient_diagonal_spectrum
    (H : HomogeneousSource S G)
    {i : ι} (J : ColourEq (CloneSAP.source S) i)
    (q : Quotient J.val) :
    originalTypedQuotientPairSpectrum (CloneSAP.source S) J J q q =
      originalEquivDiversityPalette (CloneSAP.source S) J :=
  original_quotient_diagonal_spectrum (CloneSAP.source S)
    (CloneSAP.homogeneous S H) J q

/-- B060 C35 on the actual clone source. We intersect the FULL
diversity supports of EVERY proper nonidentity MI coordinate
above the actual clone kernel (possibly with an empty type
in a degenerate single-owner sort). The result is exactly
the one genuinely realized clone atom, not logical identity.

No distributivity, NR2, quotient SAP or equivalence-lattice
exactness is assumed. -/
theorem pure_clone_all_MI_diversity_meet
    {i : ι} :
    ({a : (CloneSAP.source S).Atom i i |
        ∀ J : FullCloneProperMI S i,
          a ∈ originalEquivDiversityPalette (CloneSAP.source S) J.val} :
        (CloneSAP.source S).Menu i i) =
      ({Sum.inr ⟨rfl⟩} : (CloneSAP.source S).Menu i i) := by
  ext a
  constructor
  · intro ha
    obtain ⟨x,y,hxy⟩ := (CloneSAP.source S).realized a
    have hmi : fullCloneMIKernel S i x y := by
      intro J
      obtain ⟨p,q,hJpq,hpq⟩ := ha J
      exact (J.val.property p q x y (hpq.trans hxy.symm)).mp hJpq
    have hK : fullCloneKernel S i x y := by
      rw [← fullCloneMIKernel_eq_fullCloneKernel S i]
      exact hmi
    have howner : x.1 = y.1 := hK
    have hindex : x.2 ≠ y.2 := by
      intro hn
      have heq : x = y := Prod.ext howner hn
      subst y
      have hncol : (CloneSAP.source S).colour x x = none :=
        ((CloneSAP.source S).colour_none_iff x x).mpr rfl
      change (CloneSAP.source S).colour x x = some a at hxy
      rw [hncol] at hxy
      cases hxy
    have hc : (CloneSAP.source S).colour x y = some (Sum.inr ⟨rfl⟩) :=
      (CloneSAP.source_clone_iff S x y).mpr ⟨howner,hindex⟩
    exact Set.mem_singleton_iff.mpr (Option.some.inj (hxy.symm.trans hc))
  · intro ha J
    have hca : a = Sum.inr ⟨rfl⟩ := Set.mem_singleton_iff.mp ha
    subst a
    obtain ⟨p⟩ := S.nonemptySort i
    have hK : fullCloneKernel S i
        ((p,0) : CloneSAP.Carrier X i) (p,1) := rfl
    have hJ : J.val ((p,0) : CloneSAP.Carrier X i) (p,1) :=
      (fullCloneKernel_le_nonidentity S i J.val J.property.1) hK
    have hc : (CloneSAP.source S).colour
        ((p,0) : CloneSAP.Carrier X i) (p,1) =
          some (Sum.inr ⟨rfl⟩) := by
      apply (CloneSAP.source_clone_iff S (p,0) (p,1)).mpr
      exact ⟨rfl, by change (0 : ℕ) ≠ 1; decide⟩
    exact ⟨(p,0),(p,1),hJ,hc⟩

end CCO.CloneTupleGeometry
