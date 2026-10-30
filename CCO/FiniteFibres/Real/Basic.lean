import CCO.RealHull.Geometry.FibreCCO
import CCO.PairHomogeneity
import Mathlib.Data.Set.Finite.Range

/-! Actual real algebraicity and the selected C09/C10 fibre providers.
No finite Hasse theorem, triangle-fullness conclusion or finite-size theorem
is invoked. The full original group consists of ALL colour-preserving point
permutations, rather than an unspecified subgroup of such permutations. -/
universe v w t
namespace CCO.FiniteFibres.Real
open RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

def autGroup : Subgroup (Equiv.Perm M) where
  carrier := {g | ∀ x y, S.colour (i := ()) (j := ()) (g x) (g y) = S.colour x y}
  one_mem' := by intro x y; rfl
  mul_mem' := by intro g h hg hh x y; exact (hg (h x) (h y)).trans (hh x y)
  inv_mem' := by
    intro g hg x y
    have hh := hg (g.symm x) (g.symm y)
    simpa using hh.symm

abbrev Aut := autGroup S

variable {G : Type t} [Group G] [MulAction G M]

def motion (H : HomogeneousSource S G) (g : G) : Aut S :=
  ⟨MulAction.toPerm g,fun x y => S.colourInvariant_of_homogeneous H g x y⟩

theorem fullHomogeneous (H : HomogeneousSource S G) : HomogeneousSource S (Aut S) where
  preserves_sort := by rintro g ⟨i,x⟩; cases i; rfl
  preserves_colours := by
    rintro g ⟨i,x⟩ ⟨j,y⟩
    cases i; cases j
    exact congrArg (fun c => (⟨(),(),c⟩ : Σ i : Unit, Σ j : Unit, Option (S.Atom i j)))
      (g.property x y)
  extends_finite_diagram := by
    intro V _ f h hc
    obtain ⟨g,hg⟩ := H.extends_finite_diagram f h hc
    refine ⟨motion S H g,fun x => ?_⟩
    cases hf : f x with | mk i a =>
      cases hh : h x with | mk j b =>
        cases i; cases j
        have hx := hg x
        rw [hf,hh] at hx
        exact hx

/-- Every same-colour ordered pair lies in one ACTUAL full-group orbital.
No CCO or finite-carrier premise is needed. -/
theorem actual_pair_orbit (H : HomogeneousSource S G) (x y x' y' : M) :
    S.colour (i := ()) (j := ()) x y = S.colour x' y' ↔
      ∃ g : Aut S, g • x = x' ∧ g • y = y' := by
  constructor
  · exact S.pair_homogeneous_of_homogeneous (fullHomogeneous S H) x x' y y'
  · rintro ⟨g,rfl,rfl⟩
    exact (g.property x y).symm

def orbitOver (A : Finset M) (x : M) : Set M :=
  {y | ∃ g : Aut S, (∀ a ∈ A, g • a = a) ∧ g • x = y}

def acl (A : Finset M) : Set M := {x | (orbitOver S A x).Finite}

theorem parameter_mem_acl (A : Finset M) {x : M} (hx : x ∈ A) : x ∈ acl S A := by
  apply (Set.finite_singleton x).subset
  rintro y ⟨g,hg,rfl⟩
  exact Set.mem_singleton_iff.mpr (hg x hx)

theorem self_mem_orbit (A : Finset M) (x : M) : x ∈ orbitOver S A x :=
  ⟨1,fun _ _ => one_smul _ _,one_smul _ _⟩

variable [DecidableEq M]

noncomputable def spokes (A : Finset M) (x : M) (hx : x ∉ A) : ↥A → Atom S :=
  fun a => (col_some_of_ne S (x := x) (y := a.val) (fun h => hx (h.symm ▸ a.property))).choose

theorem spokes_colour (A : Finset M) (x : M) (hx : x ∉ A) (a : ↥A) :
    col S x a.val = some (spokes S A x hx a) :=
  (col_some_of_ne S (x := x) (y := a.val) (fun h => hx (h.symm ▸ a.property))).choose_spec

def fibrePoint (A : Finset M) (x : M) (hx : x ∉ A) : FibreSet S A (spokes S A x hx) :=
  ⟨x,spokes_colour S A x hx⟩

theorem orbit_eq_fibre (H : HomogeneousSource S G)
    (A : Finset M) (x : M) (hx : x ∉ A) :
    orbitOver S A x = FibreSet S A (spokes S A x hx) :=
  fibre_orbit_eq S A (spokes S A x hx) (fullHomogeneous S H) (fibrePoint S A x hx)

theorem algebraic_iff_finite_fibre (H : HomogeneousSource S G)
    (A : Finset M) (x : M) (hx : x ∉ A) :
    x ∈ acl S A ↔ (FibreSet S A (spokes S A x hx)).Finite := by
  change (orbitOver S A x).Finite ↔ _
  rw [orbit_eq_fibre S H A x hx]

theorem acl_eq_anchor_union_finite_fibres (H : HomogeneousSource S G) (A : Finset M) :
    acl S A = (A : Set M) ∪
      {x | ∃ q : ↥A → Atom S, (FibreSet S A q).Finite ∧ x ∈ FibreSet S A q} := by
  ext x
  constructor
  · intro hx
    by_cases hxA : x ∈ A
    · exact Or.inl hxA
    · exact Or.inr ⟨spokes S A x hxA,(algebraic_iff_finite_fibre S H A x hxA).mp hx,
        spokes_colour S A x hxA⟩
  · rintro (hxA | ⟨q,hfin,hq⟩)
    · exact parameter_mem_acl S A hxA
    · have hxA : x ∉ A := fibre_not_anchor S A q ⟨x,hq⟩
      have horbit : orbitOver S A x = FibreSet S A q :=
        fibre_orbit_eq S A q (fullHomogeneous S H) ⟨x,hq⟩
      change (orbitOver S A x).Finite
      rwa [horbit]

theorem fibre_disjoint (A : Finset M) {q r : ↥A → Atom S} (hqr : q ≠ r) :
    Disjoint (FibreSet S A q) (FibreSet S A r) := by
  apply Set.disjoint_left.mpr
  intro x hx hy
  apply hqr
  funext a
  exact Option.some.inj ((hx a).symm.trans (hy a))

theorem empty_orbit (H : HomogeneousSource S G) (x : M) : orbitOver S ∅ x = Set.univ := by
  ext y
  constructor
  · intro _; trivial
  · intro _
    obtain ⟨g,hg⟩ := S.original_sort_transitive_of_homogeneous (fullHomogeneous S H) () x y
    exact ⟨g,fun a ha => False.elim (Finset.notMem_empty a ha),hg⟩

theorem empty_acl_infinite (H : HomogeneousSource S G) [Infinite M] : acl S ∅ = ∅ := by
  ext x
  change (orbitOver S ∅ x).Finite ↔ False
  rw [empty_orbit S H x]
  exact ⟨fun h => Set.infinite_univ h,False.elim⟩

theorem acl_finite_source [Finite M] (A : Finset M) : acl S A = Set.univ := by
  ext x
  exact iff_of_true (Set.toFinite _) trivial

end CCO.FiniteFibres.Real
