import CCO.ParityHasse.Original.Equivalences
import CCO.PairHomogeneity
import Mathlib.Order.ModularLattice

/-!
# Actual SAP-free original orbital algebra

All colour-invariant relations (not only equivalences or exact profiles)
are symmetric, invariant and commuting. Only finite homogeneity is used;
there is no SAP, CCO or RAW exact-Helly premise.
-/
universe u v w t
namespace CCO.ParityHasse.Original
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X) {i : ι}
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- Same-sort actual colours, including genuine equality, are symmetric. -/
theorem colour_symmetric (x y : X i) : S.colour x y = S.colour y x := by
  calc
    S.colour x y = (S.colour y x).map S.conv := S.colour_reverse y x
    _ = S.colour y x := by
      cases h : S.colour y x with
      | none => rfl
      | some a => simp only [Option.map_some, S.symmetricLoop]

theorem colourInvariant_symmetric {R : X i → X i → Prop}
    (hR : ColourInvariant S i R) : ∀ x y, R x y → R y x := by
  intro x y hxy
  exact (hR x y y x (colour_symmetric S x y)).mp hxy

theorem colourInvariant_groupInvariant (H : HomogeneousSource S G)
    {R : X i → X i → Prop} (hR : ColourInvariant S i R) :
    ∀ (g : G) x y, R x y → R (g • x) (g • y) := by
  intro g x y hxy
  exact (hR x y (g • x) (g • y)
    (S.colourInvariant_of_homogeneous H g x y).symm).mp hxy

theorem groupInvariant_colourInvariant (H : HomogeneousSource S G)
    {R : X i → X i → Prop}
    (hR : ∀ (g : G) x y, R x y → R (g • x) (g • y)) :
    ColourInvariant S i R := by
  intro x y x' y' hcol
  obtain ⟨g, hgx, hgy⟩ := S.pair_homogeneous_of_homogeneous H x x' y y' hcol
  constructor
  · intro hxy
    simpa only [hgx, hgy] using hR g x y hxy
  · intro hx'y'
    have h := hR g⁻¹ x' y' hx'y'
    rw [← hgx, ← hgy] at h
    simpa only [inv_smul_smul] using h

theorem colourInvariant_comp (H : HomogeneousSource S G)
    {R T : X i → X i → Prop}
    (hR : ColourInvariant S i R) (hT : ColourInvariant S i T) :
    ColourInvariant S i (RawSymmetric.compose R T) := by
  apply groupInvariant_colourInvariant S H
  rintro g x y ⟨z, hxz, hzy⟩
  exact ⟨g • z, colourInvariant_groupInvariant S H hR g x z hxz,
    colourInvariant_groupInvariant S H hT g z y hzy⟩

/-- Symmetry of ALL invariant relations, including represented products,
is what justifies commutation; symmetry of equivalences alone is insufficient. -/
theorem invariant_relations_commute (H : HomogeneousSource S G)
    {R T : X i → X i → Prop}
    (hR : ColourInvariant S i R) (hT : ColourInvariant S i T) :
    RawSymmetric.compose R T = RawSymmetric.compose T R :=
  RawSymmetric.invariant_commute R T
    (colourInvariant_groupInvariant S H hR)
    (colourInvariant_groupInvariant S H hT) (S.pair_flip_of_homogeneous H)

theorem invariant_nonempty_serial (H : HomogeneousSource S G)
    {R : X i → X i → Prop} (hR : ColourInvariant S i R)
    (hne : ∃ x y, R x y) : ∀ x, ∃ y, R x y :=
  TRel.invariant_serial R (S.original_sort_transitive_of_homogeneous H i)
    (colourInvariant_groupInvariant S H hR) hne

theorem invariant_nonempty_coserial (H : HomogeneousSource S G)
    {R : X i → X i → Prop} (hR : ColourInvariant S i R)
    (hne : ∃ x y, R x y) : ∀ y, ∃ x, R x y :=
  TRel.invariant_coserial R (S.original_sort_transitive_of_homogeneous H i)
    (colourInvariant_groupInvariant S H hR) hne

/-- Actual setoid join is its represented relational product. -/
theorem sup_relation_iff (H : HomogeneousSource S G)
    (E F : ColourEq S i) (x y : X i) :
    (E.val ⊔ F.val) x y ↔ ∃ z, E x z ∧ F z y := by
  have h := RawSymmetric.comp_equivalences_is_join E F
    ⟨E.val.refl, fun _ _ h => E.val.symm h, fun _ _ _ h k => E.val.trans h k⟩
    ⟨F.val.refl, fun _ _ h => F.val.symm h, fun _ _ _ h k => F.val.trans h k⟩
    (colourInvariant_groupInvariant S H E.2)
    (colourInvariant_groupInvariant S H F.2) (S.pair_flip_of_homogeneous H)
  let K : Setoid (X i) :=
    { r := RawSymmetric.compose E F
      iseqv := ⟨h.1.refl, fun {x y} hxy => h.1.symm x y hxy,
        fun {x y z} hxy hyz => h.1.trans x y z hxy hyz⟩ }
  have hsup : E.val ⊔ F.val = K := by
    apply le_antisymm
    · exact sup_le (fun _ _ hxy => h.2.1 _ _ hxy) (fun _ _ hxy => h.2.2.1 _ _ hxy)
    · rintro a b ⟨z, haz, hzb⟩
      exact (E.val ⊔ F.val).trans ((show E.val ≤ E.val ⊔ F.val from le_sup_left) haz) ((show F.val ≤ E.val ⊔ F.val from le_sup_right) hzb)
  rw [hsup]
  exact Iff.rfl

namespace ColourEq

/-- The join remains in the FULL original colour-invariant family. -/
def join (H : HomogeneousSource S G) (E F : ColourEq S i) : ColourEq S i :=
  ⟨E.val ⊔ F.val, by
    have hc := colourInvariant_comp S H E.2 F.2
    intro x y x' y' hcol
    rw [sup_relation_iff S H E F, sup_relation_iff S H E F]
    exact hc x y x' y' hcol⟩

/-- This lattice instance is explicit in its source homogeneity witness. -/
@[instance_reducible] def lattice (H : HomogeneousSource S G) : Lattice (ColourEq S i) where
  __ := (inferInstance : SemilatticeInf (ColourEq S i))
  sup := join S H
  le_sup_left := by
    intro E F
    change E.val ≤ E.val ⊔ F.val
    exact le_sup_left
  le_sup_right := by
    intro E F
    change F.val ≤ E.val ⊔ F.val
    exact le_sup_right
  sup_le := by
    intro E F K hE hF
    change E.val ⊔ F.val ≤ K.val
    exact sup_le hE hF

/-- Full invariant equivalences form a modular lattice because their
actual represented products commute. No endpoint exactness is imposed. -/
def modular (H : HomogeneousSource S G) :
    letI := lattice S H (i := i)
    IsModularLattice (ColourEq S i) := by
  letI := lattice S H (i := i)
  constructor
  intro E F K hEK x z hxz
  obtain ⟨y, hxy, hyz⟩ := (sup_relation_iff S H E F x z).mp hxz.1
  have hKy : K x y := hEK hxy
  have hyzK : K y z := K.val.trans (K.val.symm hKy) hxz.2
  exact (sup_relation_iff S H E (F ⊓ K) x z).mpr ⟨y, hxy, hyz, hyzK⟩

end ColourEq
end CCO.ParityHasse.Original
