import CCO.PairHomogeneity
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Set.Finite.Range

/-!
# The actual finite orbital palette of equivariant quotient sorts

All sorts here are actual equivariant surjective images of one original
sort. Diversity atoms are actual group orbitals of tagged-distinct pairs;
the real tagged diagonal is `none`. Finiteness follows from the original
finite optional palette and original pair homogeneity. No quotient
homogeneity, exactness, SAP or CCO is assumed by this construction.
-/

universe u v w z q t

namespace CCO.RawExact.QuotientPalette

variable {G : Type t} [Group G]

theorem orbital_eq_of_mem {A : Type*} {B : Type*}
    [MulAction G A] [MulAction G B] {a x : A} {b y : B}
    (h : GroupActions.orbital (G := G) a b x y) :
    GroupActions.orbital (G := G) x y = GroupActions.orbital (G := G) a b := by
  obtain ⟨g, rfl, rfl⟩ := h
  funext p r
  apply propext
  constructor
  · rintro ⟨h, hp, hr⟩
    exact ⟨h * g, by simpa only [mul_smul] using hp,
      by simpa only [mul_smul] using hr⟩
  · rintro ⟨h, hp, hr⟩
    exact ⟨h * g⁻¹, by simpa only [mul_smul, inv_smul_smul] using hp,
      by simpa only [mul_smul, inv_smul_smul] using hr⟩

theorem orbital_swap_iff {A : Type*} {B : Type*}
    [MulAction G A] [MulAction G B] (a x : A) (b y : B) :
    GroupActions.orbital (G := G) b a y x ↔
      GroupActions.orbital (G := G) a b x y := by
  constructor <;> rintro ⟨g, h₁, h₂⟩ <;> exact ⟨g, h₂, h₁⟩

variable {K : Type z} (Q : K → Type q) [∀ k, MulAction G (Q k)]

def DiversityAtom (k l : K) :=
  {R : Q k → Q l → Prop //
    (∃ x y, R = GroupActions.orbital (G := G) x y) ∧
    ∀ x y, R x y → (⟨k, x⟩ : Sigma Q) ≠ ⟨l, y⟩}

def converse {k l : K} (a : DiversityAtom (G := G) Q k l) :
    DiversityAtom (G := G) Q l k := by
  refine ⟨fun y x => a.val x y, ?_, ?_⟩
  · obtain ⟨x, y, hR⟩ := a.property.1
    refine ⟨y, x, ?_⟩
    funext p r
    rw [hR]
    exact propext (orbital_swap_iff x r y p).symm
  · intro y x hxy heq
    exact a.property.2 x y hxy heq.symm

theorem converse_invol {k l : K} (a : DiversityAtom (G := G) Q k l) :
    converse Q (converse Q a) = a := by
  apply Subtype.ext
  rfl

def pairAtom {k l : K} (x : Q k) (y : Q l)
    (hne : (⟨k, x⟩ : Sigma Q) ≠ ⟨l, y⟩) :
    DiversityAtom (G := G) Q k l := by
  refine ⟨GroupActions.orbital (G := G) x y, ⟨x, y, rfl⟩, ?_⟩
  rintro a b ⟨g, hgx, hgy⟩ hab
  have hEq : g • (⟨k, x⟩ : Sigma Q) = g • (⟨l, y⟩ : Sigma Q) := by
    change (⟨k, g • x⟩ : Sigma Q) = ⟨l, g • y⟩
    simpa only [hgx, hgy] using hab
  have h := congrArg (fun p : Sigma Q => g⁻¹ • p) hEq
  exact hne (by simpa only [inv_smul_smul] using h)

noncomputable def colour {k l : K} (x : Q k) (y : Q l) :
    Option (DiversityAtom (G := G) Q k l) := by
  classical
  exact if h : (⟨k, x⟩ : Sigma Q) = ⟨l, y⟩ then none
    else some (pairAtom Q x y h)

theorem colour_none_iff {k l : K} (x : Q k) (y : Q l) :
    colour (G := G) Q x y = none ↔ (⟨k, x⟩ : Sigma Q) = ⟨l, y⟩ := by
  classical
  unfold colour
  split <;> simp_all

theorem colour_some_iff {k l : K} (x : Q k) (y : Q l)
    (a : DiversityAtom (G := G) Q k l) :
    colour Q x y = some a ↔ a.val = GroupActions.orbital (G := G) x y := by
  classical
  by_cases h : (⟨k, x⟩ : Sigma Q) = ⟨l, y⟩
  · constructor
    · intro hc
      simp [colour, h] at hc
    · intro hR
      have hne := a.property.2 x y
        (by rw [hR]; exact GroupActions.orbital_nonempty x y)
      exact False.elim (hne h)
  · simp only [colour, dite_eq_right h, Option.some.injEq]
    constructor
    · intro heq
      exact (congrArg Subtype.val heq).symm
    · intro hR
      apply Subtype.ext
      exact hR.symm

theorem colour_swap {k l : K} (x : Q k) (y : Q l)
    (a : DiversityAtom (G := G) Q k l) :
    colour Q x y = some a ↔ colour Q y x = some (converse Q a) := by
  rw [colour_some_iff, colour_some_iff]
  constructor
  · intro hR
    funext p r
    change a.val r p = GroupActions.orbital (G := G) y x p r
    rw [hR]
    exact propext (orbital_swap_iff x r y p).symm
  · intro hR
    funext p r
    have h := congrFun (congrFun hR r) p
    change a.val p r = GroupActions.orbital (G := G) y x r p at h
    exact h.trans (propext (orbital_swap_iff x p y r))

section Original

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable [∀ i, MulAction G (X i)] (H : HomogeneousSource S G)
variable {i : ι} (π : ∀ k, X i → Q k)
variable (surjπ : ∀ k, Function.Surjective (π k))
variable (equivπ : ∀ k (g : G) x, π k (g • x) = g • π k x)

theorem optional_colour_realized (c : Option (S.Atom i i)) :
    ∃ p : X i × X i, S.colour p.1 p.2 = c := by
  cases c with
  | none =>
      obtain ⟨x⟩ := S.nonemptySort i
      exact ⟨(x, x), (S.colour_none_iff x x).mpr rfl⟩
  | some a =>
      obtain ⟨x, y, hxy⟩ := S.realized a
      exact ⟨(x, y), hxy⟩

noncomputable def colourRepresentatives (c : Option (S.Atom i i)) : X i × X i :=
  Classical.choose (optional_colour_realized S c)

theorem colourRepresentatives_spec (c : Option (S.Atom i i)) :
    S.colour (colourRepresentatives S c).1 (colourRepresentatives S c).2 = c :=
  Classical.choose_spec (optional_colour_realized S c)

include S H π surjπ equivπ

theorem finite_diversity_atoms (k l : K) :
    Finite (DiversityAtom (G := G) Q k l) := by
  classical
  let : Fintype (S.Atom i i) := S.finiteAtom i i
  let f : Option (S.Atom i i) → (Q k → Q l → Prop) := fun c =>
    GroupActions.orbital (G := G)
      (π k (colourRepresentatives S c).1) (π l (colourRepresentatives S c).2)
  have hfinite : (Set.range f).Finite := Set.finite_range f
  have hsub : {R : Q k → Q l → Prop |
      (∃ x y, R = GroupActions.orbital (G := G) x y) ∧
      ∀ x y, R x y → (⟨k, x⟩ : Sigma Q) ≠ ⟨l, y⟩} ⊆ Set.range f := by
    rintro R ⟨⟨x, y, rfl⟩, _⟩
    obtain ⟨a, rfl⟩ := surjπ k x
    obtain ⟨b, rfl⟩ := surjπ l y
    let c := S.colour a b
    have hc := colourRepresentatives_spec S c
    obtain ⟨g, hga, hgb⟩ :=
      (S.pair_homogeneous_of_homogeneous H)
        (colourRepresentatives S c).1 a (colourRepresentatives S c).2 b hc
    refine ⟨c, ?_⟩
    exact (orbital_eq_of_mem (G := G)
      ⟨g, by rw [← equivπ k g _, hga], by rw [← equivπ l g _, hgb]⟩).symm
  exact (hfinite.subset hsub).to_subtype

theorem quotient_transitive (k : K) (x y : Q k) : ∃ g : G, g • x = y := by
  obtain ⟨a, rfl⟩ := surjπ k x
  obtain ⟨b, rfl⟩ := surjπ k y
  obtain ⟨g, hg⟩ := S.original_sort_transitive_of_homogeneous H i a b
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
        obtain ⟨g, hg⟩ := quotient_transitive Q S H π surjπ equivπ k x x'
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

theorem colour_invariant {k l : K} (g : G) (x : Q k) (y : Q l) :
    colour (G := G) Q (g • x) (g • y) = colour Q x y :=
  ((colour_eq_iff_orbital Q S H π surjπ equivπ x y (g • x) (g • y)).mpr
    ⟨g, rfl, rfl⟩).symm

/-- The actual quotient orbital source. Its finite palette and real
diagonal are proved, without assuming quotient homogeneity or CCO. -/
noncomputable def actualQuotientAtomicSource [Fintype K] : AtomicSource K Q := by
  classical
  refine {
    Atom := DiversityAtom (G := G) Q
    finiteSort := inferInstance
    finiteAtom := ?_
    nonemptySort := ?_
    conv := converse Q
    conv_invol := ?_
    symmetricLoop := ?_
    colour := colour Q
    colour_none_iff := colour_none_iff Q
    colour_swap := colour_swap Q
    realized := ?_
  }
  · intro k l
    letI : Finite (DiversityAtom (G := G) Q k l) :=
      finite_diversity_atoms Q S H π surjπ equivπ k l
    exact Fintype.ofFinite _
  · intro k
    obtain ⟨x⟩ := S.nonemptySort i
    exact ⟨π k x⟩
  · intro k l a
    exact converse_invol Q a
  · intro k a
    exact converse_loop Q S H π surjπ equivπ k a
  · intro k l a
    obtain ⟨x, y, hR⟩ := a.property.1
    exact ⟨x, y, (colour_some_iff Q x y a).mpr hR⟩

theorem actualQuotientAtomicSource_colour_eq_iff_orbital [Fintype K]
    {k l : K} (x : Q k) (y : Q l) (x' : Q k) (y' : Q l) :
    (actualQuotientAtomicSource Q S H π surjπ equivπ).colour x y =
      (actualQuotientAtomicSource Q S H π surjπ equivπ).colour x' y' ↔
      GroupActions.orbital (G := G) x y x' y' :=
  colour_eq_iff_orbital Q S H π surjπ equivπ x y x' y'

theorem actualQuotientAtomicSource_colour_invariant [Fintype K]
    {k l : K} (g : G) (x : Q k) (y : Q l) :
    (actualQuotientAtomicSource Q S H π surjπ equivπ).colour (g • x) (g • y) =
      (actualQuotientAtomicSource Q S H π surjπ equivπ).colour x y :=
  colour_invariant Q S H π surjπ equivπ g x y

end Original

end CCO.RawExact.QuotientPalette

namespace CCO.RawExact
export QuotientPalette (actualQuotientAtomicSource)
end CCO.RawExact
