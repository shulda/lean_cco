import CCO.CloneSAP.Lattice.Palettes
import CCO.QuotientTransport.Definability

/-! C27/C28: genuine parameter-free first-order formulas in the original
finite named language, including formulas of arbitrary quantifier depth. -/

universe u v w t
namespace CCO.CloneSAP.Lattice
open CCO.ParityHasse.Original
open CCO.QuotientTransport.Definability
open FirstOrder FirstOrder.Language
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

private theorem tagged_atom_motion (H : HomogeneousSource S G) (g : G)
    {i j : ι} (c : Option (S.Atom i j)) (p q : Sigma X) :
    taggedRelation (fun x : X i => fun y : X j => S.colour x y = c) p q →
      taggedRelation (fun x : X i => fun y : X j => S.colour x y = c) (g • p) (g • q) := by
  rintro ⟨x, y, rfl, rfl, hc⟩
  exact ⟨g • x, g • y, rfl, rfl, (S.colourInvariant_of_homogeneous H g x y).trans hc⟩

/-- Each original homogeneous-source automorphism is an automorphism of
the actual named first-order structure, with no definability premise. -/
def namedAut (H : HomogeneousSource S G) (g : G) :
    (Sigma X) ≃[namedLanguage S] (Sigma X) where
  toEquiv := MulAction.toPerm g
  map_fun' f := Empty.elim f
  map_rel' r := by
    cases r with
    | sortName i => intro x; exact Iff.rfl
    | pairName i j c =>
      intro x
      change taggedRelation (fun a : X i => fun b : X j => S.colour a b = c)
        (g • x 0) (g • x 1) ↔
        taggedRelation (fun a : X i => fun b : X j => S.colour a b = c) (x 0) (x 1)
      constructor
      · intro h
        have hh := tagged_atom_motion S H g⁻¹ c _ _ h
        change taggedRelation (fun a : X i => fun b : X j => S.colour a b = c)
          (g⁻¹ • (g • x 0)) (g⁻¹ • (g • x 1)) at hh
        simpa only [inv_smul_smul] using hh
      · exact tagged_atom_motion S H g c _ _

/-- Any first-order definable relation is invariant under the actual
source group; this uses the semantics theorem, not a formula oracle. -/
theorem formula_invariant (H : HomogeneousSource S G) {i j : ι}
    (R : TRel X i j) (hR : TypedHasFormula (L := namedLanguage S) R) :
    TRel.Invariant (G := G) R := by
  obtain ⟨φ, hφ⟩ := hR
  intro g x y hxy
  have hOld : φ.Realize ![(⟨i, x⟩ : Sigma X), ⟨j, y⟩] :=
    (hφ _ _).mpr ⟨x, y, rfl, rfl, hxy⟩
  have hNew := (StrongHomClass.realize_formula (namedAut S H g) φ).mpr hOld
  have hVal : (namedAut S H g) ∘ ![(⟨i, x⟩ : Sigma X), ⟨j, y⟩] =
      ![(⟨i, g • x⟩ : Sigma X), ⟨j, g • y⟩] := by
    funext k
    fin_cases k <;> rfl
  rw [hVal] at hNew
  obtain ⟨a, b, ha, hb, hab⟩ := (hφ _ _).mp hNew
  have heA : g • x = a := by simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using ha
  have heB : g • y = b := by simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hb
  simpa only [← heA, ← heB] using hab

/-- Every palette union is defined by a finite original-language formula. -/
theorem palette_has_formula (H : HomogeneousSource S G) (i : ι) (P : Palette S i) :
    TypedHasFormula (L := namedLanguage S) (relation S i P.val) :=
  source_invariant_has_formula S H _
    (colourInvariant_groupInvariant S H (relation_invariant S i P.val))

/-- The two-point map gives exactly one actual pair orbital for every
named occurring colour, including equality through repeated tuples. -/
theorem colour_iff_pair_orbit (H : HomogeneousSource S G) {i j : ι}
    (x x' : X i) (y y' : X j) :
    S.colour x y = S.colour x' y' ↔ ∃ g : G, g • x = x' ∧ g • y = y' := by
  constructor
  · exact S.pair_homogeneous_of_homogeneous H x x' y y'
  · rintro ⟨g, rfl, rfl⟩
    exact (S.colourInvariant_of_homogeneous H g x y).symm

/-- Selected source result prop:lattice-interface, definability part.
Uniqueness is of actual occurring diversity palettes, not syntactic names. -/
theorem definable_equivalence_palette (H : HomogeneousSource S G) (i : ι)
    (E : Setoid (X i)) (hE : TypedHasFormula (L := namedLanguage S) E) :
    ∃! P : Palette S i, ∀ x y, relation S i P.val x y ↔ E x y := by
  let C : ColourEq S i := ⟨E, groupInvariant_colourInvariant S H
    (formula_invariant S H E hE)⟩
  refine ⟨ofColourEq S i C, relation_paletteOf S i C, ?_⟩
  intro P hP
  have eq : toColourEq S i P = C := ColourEq.ext S i hP
  have hh := congrArg (ofColourEq S i) eq
  simpa only [of_to] using hh

/-- Invariant equivalences have the same unique palettes, even without
being supplied a formula in advance. Their formulas are constructed above. -/
theorem invariant_equivalence_palette (H : HomogeneousSource S G) (i : ι)
    (E : Setoid (X i)) (hE : TRel.Invariant (G := G) E) :
    ∃! P : Palette S i, ∀ x y, relation S i P.val x y ↔ E x y :=
  definable_equivalence_palette S H i E (source_invariant_has_formula S H E hE)

end CCO.CloneSAP.Lattice
