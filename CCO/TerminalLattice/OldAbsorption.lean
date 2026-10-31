import CCO.TerminalLattice.StrongPaletteBridge
import CCO.StabilizerSAP
import CCO.SAPPoint
import Mathlib.Data.Finset.Basic

/-!
# B050 C24: absorption by a NONZERO ORIGINAL equivalence diversity menu

An arbitrary nonempty original same-sort STRONG menu D inside Kᵒ is
absorbed by Kᵒ on both sides. This is a source result with ORIGINAL
homogeneity + actual visible AgeSAP, but WITHOUT CCO, NR2,
distributivity, exactness, quotient homogeneity or a new axiom.

The single nontrivial step is genuinely finding a D-coloured old real
neighbour of an arbitrary pinned endpoint outside any prescribed finite
set. We derive that fact from accepted B001 stabilizer-orbit freshness,
fixing the old endpoint as a COMPLETE one-point base.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse.Original

/-- Every original diversity orbital has arbitrarily many REAL
neighbours of EVERY old real point, outside an arbitrary finite set.
No class-infiniteness axiom or unrestricted orbit extension is assumed. -/
theorem original_atom_neighbour_avoiding
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (d : S.Atom i i)
    (z : X i) (forbidden : Finset (X i)) :
    ∃ y : X i, y ∉ forbidden ∧ S.atomRel d y z := by
  classical
  obtain ⟨p, q, hpq⟩ := S.realized d
  obtain ⟨g, hgq⟩ :=
    S.original_sort_transitive_of_homogeneous H i q z
  let w₀ : X i := g • p
  have hwz : S.atomRel d w₀ z := by
    have hmove := S.colourInvariant_of_homogeneous H g p q
    simpa only [w₀, hgq] using hmove.trans hpq
  have hwne : w₀ ≠ z := by
    intro h
    exact S.atomRel_ne hwz (congrArg (Sigma.mk i) h)
  let anchor : Sigma X := ⟨i, z⟩
  let base : FiniteInduced (X := X) :=
    FiniteInduced.ofFinset ({anchor} : Finset (Sigma X))
  have hAnchor : anchor ∈ base.vertices := by
    simp [base, FiniteInduced.ofFinset]
  have hNotBase : (⟨i, w₀⟩ : Sigma X) ∉ base.vertices := by
    intro h
    have hh : w₀ = z := by
      simpa [base, FiniteInduced.ofFinset, anchor] using h
    exact hwne hh
  let forbiddenTag : Set (Sigma X) :=
    (fun x : X i => (⟨i, x⟩ : Sigma X)) '' (↑forbidden : Set (X i))
  have hFinite : forbiddenTag.Finite := forbidden.finite_toSet.image _
  obtain ⟨yTag, hyOrbit, hyNot⟩ :=
    RealAction.orbit_has_fresh_point_of_SAP S H sap base
      (⟨i, w₀⟩ : Sigma X) hNotBase forbiddenTag hFinite
  obtain ⟨k, hkFix, hkw⟩ := hyOrbit
  have hSort : yTag.1 = i := by
    calc
      yTag.1 = (k • (⟨i,w₀⟩ : Sigma X)).1 :=
        congrArg Sigma.fst hkw.symm
      _ = i := by simp only [Sigma.smul_mk]
  obtain ⟨y, hyTag⟩ := tagged_exists_of_sort (X := X) yTag i hSort
  have hFixAnchor : k • anchor = anchor :=
    (RealAction.mem_pointwiseStabilizer base.vertices k).mp
      hkFix anchor hAnchor
  have hkz : k • z = z := by
    simpa only [anchor, Sigma.smul_mk, Sigma.mk.injEq,
      heq_eq_eq, true_and] using hFixAnchor
  have hkwy : k • w₀ = y := by
    rw [hyTag] at hkw
    simpa only [Sigma.smul_mk, Sigma.mk.injEq,
      heq_eq_eq, true_and] using hkw
  have hyz : S.atomRel d y z := by
    have hm := S.colourInvariant_of_homogeneous H k w₀ z
    simpa only [hkwy, hkz] using hm.trans hwz
  refine ⟨y, ?_, hyz⟩
  intro h
  exact hyNot ⟨y, h, hyTag.symm⟩

/-- SOURCE C24 `eq:typed-old-reset-absorption`: if D is any nonempty
OLD fine-diversity subpalette of a genuinely invariant K-class menu,
then Kᵒ star D = Kᵒ, as literal original three-point STRONG atom
palettes. This handles arbitrary D without asserting it is exact,
one-word, or that it has a particular homogeneous representative. -/
theorem original_equiv_diversity_absorbs
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    (D : S.Menu i i)
    (hD : D.Nonempty)
    (hDK : D ⊆ originalEquivDiversityPalette S K) :
    S.product (originalEquivDiversityPalette S K) D =
      originalEquivDiversityPalette S K := by
  classical
  apply Set.Subset.antisymm
  · intro c hc
    obtain ⟨a, ha, d, hd, x, y, z, hxy, hyz, hxz⟩ := hc
    obtain ⟨p, q, hKpq, hpq⟩ := ha
    obtain ⟨u, v, hKuv, huv⟩ := hDK hd
    have hKxy : K x y :=
      (K.property p q x y (hpq.trans hxy.symm)).mp hKpq
    have hKyz : K y z :=
      (K.property u v y z (huv.trans hyz.symm)).mp hKuv
    exact ⟨x, z, K.val.trans hKxy hKyz, hxz⟩
  · intro c hc
    obtain ⟨x, z, hKxz, hxz⟩ := hc
    obtain ⟨d, hd⟩ := hD
    obtain ⟨y, hyAvoid, hyz⟩ :=
      original_atom_neighbour_avoiding
        S H sap d z ({x,z} : Finset (X i))
    have hxyNe : x ≠ y := by
      intro heq
      exact hyAvoid (by simp [heq])
    have hTagged : (⟨i, x⟩ : Sigma X) ≠ ⟨i, y⟩ := by
      intro hh
      have heq : x = y := by
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hh
      exact hxyNe heq
    obtain ⟨a, hxy⟩ := S.some_colour_of_ne x y hTagged
    obtain ⟨u, v, hKuv, huv⟩ := hDK hd
    have hKyz : K y z :=
      (K.property u v y z (huv.trans hyz.symm)).mp hKuv
    have hKxy : K x y := K.val.trans hKxz (K.val.symm hKyz)
    have ha : a ∈ originalEquivDiversityPalette S K :=
      ⟨x, y, hKxy, hxy⟩
    exact ⟨a, ha, d, hd, x, y, z, hxy, hyz, hxz⟩

/-- The other OLD STRONG product orientation has the SAME absorption
identity. Only original same-sort symmetry is used to reverse factors;
there is no mixed-sort commutation assertion. -/
theorem original_equiv_diversity_absorbs_right
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {i : ι} (K : ColourEq S i)
    (D : S.Menu i i)
    (hD : D.Nonempty)
    (hDK : D ⊆ originalEquivDiversityPalette S K) :
    S.product D (originalEquivDiversityPalette S K) =
      originalEquivDiversityPalette S K := by
  calc
    S.product D (originalEquivDiversityPalette S K) =
        S.product (originalEquivDiversityPalette S K) D :=
      S.loop_product_commute D (originalEquivDiversityPalette S K)
    _ = originalEquivDiversityPalette S K :=
      original_equiv_diversity_absorbs S H sap K D hD hDK

end CCO.TerminalLattice
