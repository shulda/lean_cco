import CCO.ParityHasse.Original.OrbitalAlgebra

/-!
# B050: original same-sort modularity and the actual M₃ class obstruction

The original ambient automorphism action, not a larger reduct automorphism
group, is used through `HomogeneousSource`. In particular these RAW facts
do not require SAP, CCO, NR2 or representation by exact words.

Source: sections/v27/08_typed_terminal_reset_equivalences.tex,
frozen source commit 490c3f36d85db5a0b3ced0598e6c431825254ec5.
B050 C01–C03 reuse the accepted B006 original-colour providers;
C06 is an independent class-intersection argument for *actual*
invariant equivalences, not an abstract formal lattice diamond.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

open ParityHasse

/-- Source `lem:typed-symmetric-orbital-commutation` (C01).
    Same-sort only; equality-inclusive RAW composition. -/
theorem original_raw_commutation (H : HomogeneousSource S G) {i : ι}
    (R T : X i → X i → Prop)
    (hR : Original.ColourInvariant S i R)
    (hT : Original.ColourInvariant S i T) :
    RawSymmetric.compose R T = RawSymmetric.compose T R :=
  Original.invariant_relations_commute S H hR hT

/-- Source `lem:typed-invariant-equivalence-modularity` (C02–C03).
    This is the FULL invariant-equivalence lattice, not the exact sublattice. -/
theorem original_full_modularity (H : HomogeneousSource S G) {i : ι} :
    letI := Original.ColourEq.lattice S H (i := i)
    IsModularLattice (Original.ColourEq S i) :=
  Original.ColourEq.modular S H

/-- B050 C06: the three classes of an actual M₃ have pairwise
intersections (witnessed by x, y, z respectively) but empty triple
intersection. A complete source pair xy will later pin these centres
in the private-word CCO obstruction (C07–C08).

No SAP, CCO, word representation or NR2 is used here. -/
theorem actual_m3_classes
    (H : HomogeneousSource S G) {i : ι}
    (E₁ E₂ E₃ L K : Original.ColourEq S i)
    (h12 : E₁ ⊓ E₂ = L)
    (h13 : E₁ ⊓ E₃ = L)
    (hjoin12 : Original.ColourEq.join S H E₁ E₂ = K)
    (hjoin23 : Original.ColourEq.join S H E₂ E₃ = K)
    (hproper : L < E₁) :
    ∃ x y z : X i,
      E₁ x y ∧ ¬ L x y ∧
      E₂ x z ∧ E₃ z y ∧
      ¬ ∃ a : X i, E₁ x a ∧ E₂ x a ∧ E₃ y a := by
  classical
  have hnot : ¬ E₁ ≤ L := not_le_of_gt hproper
  obtain ⟨x, y, hxy, hnotL⟩ :
      ∃ x y : X i, E₁ x y ∧ ¬ L x y := by
    by_contra hn
    apply hnot
    intro a b hab
    by_contra hna
    exact hn ⟨a, b, hab, hna⟩
  have hE₁K : E₁ ≤ K := by
    rw [← hjoin12]
    change E₁.val ≤ E₁.val ⊔ E₂.val
    exact le_sup_left
  have hKxy : K x y := hE₁K hxy
  have h23 : (E₂.val ⊔ E₃.val) x y := by
    change (Original.ColourEq.join S H E₂ E₃) x y
    rw [hjoin23]
    exact hKxy
  obtain ⟨z, hxz, hzy⟩ :=
    (Original.sup_relation_iff S H E₂ E₃ x y).mp h23
  refine ⟨x, y, z, hxy, hnotL, hxz, hzy, ?_⟩
  rintro ⟨a, hE₁xa, hE₂xa, hE₃ya⟩
  have hLxa : L x a := by
    have h : (E₁ ⊓ E₂) x a := ⟨hE₁xa, hE₂xa⟩
    rw [h12] at h
    exact h
  have hLya : L y a := by
    have hE₁ya : E₁ y a :=
      E₁.val.trans (E₁.val.symm hxy) hE₁xa
    have h : (E₁ ⊓ E₃) y a := ⟨hE₁ya, hE₃ya⟩
    rw [h13] at h
    exact h
  exact hnotL (L.val.trans hLxa (L.val.symm hLya))

end CCO.TerminalLattice
