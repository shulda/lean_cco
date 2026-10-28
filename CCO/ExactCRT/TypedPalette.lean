import CCO.RawExact.QuotientSourcePalette

/-!
# Actual quotient orbitals with independently typed original origins

Each quotient sort is a surjective equivariant image of its designated original
sort. Original pair homogeneity proves finite palettes even between DIFFERENT
origins. Only realized original optional colours are used in the finite cover;
in particular an impossible cross-sort logical diagonal is never realized.
No quotient homogeneity, exactness, CCO or kernel intertwining is assumed.
-/

universe u v w z q t

namespace CCO.ExactCRT.TypedPalette

open CCO.RawExact.QuotientPalette

variable {G : Type t} [Group G]
variable {K : Type z} (Q : K → Type q) [∀ k, MulAction G (Q k)]
variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable [∀ i, MulAction G (X i)] (H : HomogeneousSource S G)
variable (origin : K → ι) (π : ∀ k, X (origin k) → Q k)
variable (surjπ : ∀ k, Function.Surjective (π k))
variable (equivπ : ∀ k (g : G) x, π k (g • x) = g • π k x)

include S H π surjπ equivπ

/-- Every actual quotient orbital has a representative among a finite list of
realized ORIGINAL typed colours. No equality between distinct origins is needed.
-/
theorem finite_diversity_atoms (k l : K) :
    Finite (DiversityAtom (G := G) Q k l) := by
  classical
  letI : Fintype (S.Atom (origin k) (origin l)) := S.finiteAtom _ _
  let C := {c : Option (S.Atom (origin k) (origin l)) //
    ∃ (a : X (origin k)) (b : X (origin l)), S.colour a b = c}
  let rep : C → X (origin k) × X (origin l) := fun c =>
    ⟨Classical.choose c.property,
      Classical.choose (Classical.choose_spec c.property)⟩
  have hrep (c : C) : S.colour (rep c).1 (rep c).2 = c.val :=
    Classical.choose_spec (Classical.choose_spec c.property)
  let f : C → (Q k → Q l → Prop) := fun c =>
    GroupActions.orbital (G := G) (π k (rep c).1) (π l (rep c).2)
  have hfinite : (Set.range f).Finite := Set.finite_range f
  have hsub : {R : Q k → Q l → Prop |
      (∃ x y, R = GroupActions.orbital (G := G) x y) ∧
      ∀ x y, R x y → (⟨k, x⟩ : Sigma Q) ≠ ⟨l, y⟩} ⊆ Set.range f := by
    rintro R ⟨⟨x, y, rfl⟩, _⟩
    obtain ⟨a, rfl⟩ := surjπ k x
    obtain ⟨b, rfl⟩ := surjπ l y
    let c : C := ⟨S.colour a b, a, b, rfl⟩
    obtain ⟨g, hga, hgb⟩ :=
      (S.pair_homogeneous_of_homogeneous H) (rep c).1 a (rep c).2 b (hrep c)
    refine ⟨c, ?_⟩
    exact (orbital_eq_of_mem (G := G)
      ⟨g, by rw [← equivπ k g _, hga], by rw [← equivπ l g _, hgb]⟩).symm
  exact (hfinite.subset hsub).to_subtype

theorem quotient_transitive (k : K) (x y : Q k) : ∃ g : G, g • x = y := by
  obtain ⟨a, rfl⟩ := surjπ k x
  obtain ⟨b, rfl⟩ := surjπ k y
  obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H (origin k) a b
  exact ⟨g, by rw [← equivπ k g a, hg]⟩

theorem converse_loop (k : K) (a : DiversityAtom (G := G) Q k k) :
    converse Q a = a := by
  obtain ⟨x, y, hR⟩ := a.property.1
  obtain ⟨p, hp⟩ := surjπ k x
  obtain ⟨r, hr⟩ := surjπ k y
  obtain ⟨g, hgp, hgr⟩ := S.pair_flip_of_homogeneous H p r
  have hflip : GroupActions.orbital (G := G) x y y x := by
    refine ⟨g, ?_, ?_⟩
    · rw [← hp, ← equivπ k g p, hgp, hr]
    · rw [← hr, ← equivπ k g r, hgr, hp]
  apply Subtype.ext
  calc
    (converse Q a).val = GroupActions.orbital (G := G) y x := by
      funext p r
      change a.val r p = _
      rw [hR]
      exact propext (orbital_swap_iff x r y p).symm
    _ = GroupActions.orbital (G := G) x y := orbital_eq_of_mem hflip
    _ = a.val := hR.symm

theorem colour_eq_iff_orbital {k l : K}
    (x : Q k) (y : Q l) (x' : Q k) (y' : Q l) :
    colour (G := G) Q x y = colour Q x' y' ↔
      GroupActions.orbital (G := G) x y x' y' := by
  constructor
  · intro heq
    cases hc : colour (G := G) Q x y with
    | none =>
        have hxy := (colour_none_iff (G := G) Q x y).mp hc
        have hxy' := (colour_none_iff (G := G) Q x' y').mp (heq.symm.trans hc)
        cases hxy
        have heq' : x' = y' := by
          simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using hxy'
        subst y'
        obtain ⟨g, hg⟩ := quotient_transitive Q S H origin π surjπ equivπ k x x'
        exact ⟨g, hg, hg⟩
    | some a =>
        have ha := (colour_some_iff Q x y a).mp hc
        have ha' := (colour_some_iff Q x' y' a).mp (heq.symm.trans hc)
        have hRel : GroupActions.orbital (G := G) x y =
            GroupActions.orbital (G := G) x' y' := ha.symm.trans ha'
        rw [hRel]
        exact GroupActions.orbital_nonempty x' y'
  · intro hOrbit
    have hRel := orbital_eq_of_mem hOrbit
    cases hc : colour (G := G) Q x y with
    | none =>
        have hxy := (colour_none_iff (G := G) Q x y).mp hc
        obtain ⟨g, hgx, hgy⟩ := hOrbit
        have hxy' : (⟨k, x'⟩ : Sigma Q) = ⟨l, y'⟩ := by
          have h := congrArg (fun p : Sigma Q => g • p) hxy
          change (⟨k, g • x⟩ : Sigma Q) = ⟨l, g • y⟩ at h
          simpa only [hgx, hgy] using h
        exact ((colour_none_iff (G := G) Q x' y').mpr hxy').symm
    | some a =>
        have ha := (colour_some_iff Q x y a).mp hc
        exact ((colour_some_iff Q x' y' a).mpr (ha.trans hRel.symm)).symm

/-- The actual finite orbital language on the typed quotient family. -/
noncomputable def source [Fintype K] : AtomicSource K Q := by
  classical
  refine {
    Atom := DiversityAtom (G := G) Q
    finiteSort := inferInstance
    finiteAtom := ?_
    nonemptySort := ?_
    conv := converse Q
    conv_invol := fun a => converse_invol Q a
    symmetricLoop := ?_
    colour := colour Q
    colour_none_iff := colour_none_iff Q
    colour_swap := colour_swap Q
    realized := ?_
  }
  · intro k l
    letI : Finite (DiversityAtom (G := G) Q k l) :=
      finite_diversity_atoms Q S H origin π surjπ equivπ k l
    exact Fintype.ofFinite _
  · intro k
    obtain ⟨x⟩ := S.nonemptySort (origin k)
    exact ⟨π k x⟩
  · intro k a
    exact converse_loop Q S H origin π surjπ equivπ k a
  · intro k l a
    obtain ⟨x, y, hR⟩ := a.property.1
    exact ⟨x, y, (colour_some_iff Q x y a).mpr hR⟩

theorem source_colour_eq_iff_orbital [Fintype K]
    {k l : K} (x : Q k) (y : Q l) (x' : Q k) (y' : Q l) :
    (source Q S H origin π surjπ equivπ).colour x y =
      (source Q S H origin π surjπ equivπ).colour x' y' ↔
      GroupActions.orbital (G := G) x y x' y' :=
  colour_eq_iff_orbital Q S H origin π surjπ equivπ x y x' y'

theorem source_colour_invariant [Fintype K]
    {k l : K} (g : G) (x : Q k) (y : Q l) :
    (source Q S H origin π surjπ equivπ).colour (g • x) (g • y) =
      (source Q S H origin π surjπ equivπ).colour x y :=
  ((source_colour_eq_iff_orbital Q S H origin π surjπ equivπ x y
    (g • x) (g • y)).mpr ⟨g, rfl, rfl⟩).symm

end CCO.ExactCRT.TypedPalette
