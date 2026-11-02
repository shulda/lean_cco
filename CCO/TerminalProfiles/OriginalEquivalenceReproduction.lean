import CCO.TerminalLattice.StrongPaletteBridge
import CCO.TerminalLattice.FibreSAP
import CCO.SAPPoint

/-!
# B051 — source09 TER, actual old strong equivalence reproduction

The ambient objects are ORIGINAL transitive named old sorts and FULL
original invariant equivalences. Original SAP supplies point gluing;
original colour invariance and true equivalence transitivity guarantee
that its third atom is in the same nonzero equivalence diversity palette.

For any NONEMPTY old diversity menu C contained in J°, the original
same-sort strong triangle product satisfies
  J° * C = J° = C * J°.
With C = J°, the same statement gives J° * J° = J°.

No CCO, exactness, FULL NR2, quotient/hidden SAP, or synthetic STRONG
identity is used. The source is the frozen
sections/v27/09_typed_equivalence_and_profiles.tex: TER/C01–C04.
-/

universe u v w t

namespace CCO.TerminalProfiles

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open CCO.TerminalLattice
open ParityHasse.Original

/-- An actual old fine diversity atom in the FULL original invariant
equivalence's diversity menu relates EVERY representative pair of that
atomic colour. This is original colour invariance, not quotient
homogeneity. -/
private theorem original_equiv_atom_related
    {i : ι} (J : ColourEq S i)
    (a : S.Atom i i)
    (ha : a ∈ originalEquivDiversityPalette S J)
    (x y : X i) (hxy : S.atomRel a x y) :
    J x y := by
  obtain ⟨u, v, hJuv, huv⟩ := ha
  exact (J.property u v x y (huv.trans hxy.symm)).mp hJuv

/-- SOURCE09 C01–C03, the right-hand OLD STRONG reproduction formula.
The existence of the needed three-distinct-point triangle is derived
from the genuine original finite-age SAP point-gluing theorem; the
internal edge remains inside the actual FULL invariant equivalence. -/
theorem original_equiv_diversity_reproduction_right
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (C : S.Menu i i) (hC : C.Nonempty)
    (hCE : C ⊆ originalEquivDiversityPalette S J) :
    S.product C (originalEquivDiversityPalette S J) =
      originalEquivDiversityPalette S J := by
  let E : S.Menu i i := originalEquivDiversityPalette S J
  change S.product C E = E
  ext s
  constructor
  · rintro ⟨a, ha, b, hb, x, y, z, hxy, hyz, hxz⟩
    have hxyJ : J x y :=
      original_equiv_atom_related S J a (hCE ha) x y hxy
    have hyzJ : J y z :=
      original_equiv_atom_related S J b hb y z hyz
    exact ⟨x, z, J.val.trans hxyJ hyzJ, hxz⟩
  · intro hs
    obtain ⟨c, hc⟩ := hC
    obtain ⟨d, x, y, z, hxy, hyz, hxz⟩ :=
      (S.realPointGluing_of_SAP H sap) c s
    have hxyJ : J x y :=
      original_equiv_atom_related S J c (hCE hc) x y hxy
    have hyzJ : J y z :=
      original_equiv_atom_related S J s hs y z hyz
    have hdE : d ∈ E :=
      ⟨x, z, J.val.trans hxyJ hyzJ, hxz⟩
    have hyx : S.atomRel c y x := by
      have hSwap : S.colour y x = some (S.conv c) :=
        (S.colour_swap x y c).mp hxy
      simpa only [S.symmetricLoop c] using hSwap
    exact ⟨c, hc, d, hdE, y, x, z, hyx, hxz, hyz⟩

/-- SOURCE09 selected `lem:typed-equivalence-reproduction` / TER:
for every nonzero original invariant equivalence, its diversity
palette reproduces itself after multiplication by ANY nonempty
sub-menu, on either side. The final idempotence is the special case
C = J°. All are actual STRONG diversity-products, not RAW products. -/
theorem original_equiv_diversity_reproduction
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (J : ColourEq S i)
    (hJ : (⊥ : ColourEq S i) < J)
    (C : S.Menu i i) (hC : C.Nonempty)
    (hCE : C ⊆ originalEquivDiversityPalette S J) :
    S.product (originalEquivDiversityPalette S J) C =
        originalEquivDiversityPalette S J ∧
    S.product C (originalEquivDiversityPalette S J) =
        originalEquivDiversityPalette S J ∧
    S.product (originalEquivDiversityPalette S J)
        (originalEquivDiversityPalette S J) =
        originalEquivDiversityPalette S J := by
  let E : S.Menu i i := originalEquivDiversityPalette S J
  have hRight : S.product C E = E :=
    original_equiv_diversity_reproduction_right S H sap J C hC hCE
  have hLeft : S.product E C = E := by
    rw [S.loop_product_commute E C]
    exact hRight
  have hE : E.Nonempty := by
    obtain ⟨x, y, hJxy, hne⟩ :=
      CCO.TerminalLattice.actual_nontrivial_equiv_pair S J hJ
    cases hcol : S.colour x y with
    | none =>
        have heq : x = y := by
          have hh := (S.colour_none_iff x y).mp hcol
          simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hh
        exact False.elim (hne heq)
    | some a =>
        exact ⟨a, x, y, hJxy, hcol⟩
  have hIdem : S.product E E = E :=
    original_equiv_diversity_reproduction_right
      S H sap J E hE (by intro a ha; exact ha)
  exact ⟨hLeft, hRight, hIdem⟩

end CCO.TerminalProfiles
