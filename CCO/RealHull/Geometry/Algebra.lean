import CCO.ParityHasse.Original.OrbitalAlgebra
import CCO.RawWords

/-! Actual equality-inclusive support algebra of the original one-sort source.
The diversity guard is used only for binary rows, never as an associative
replacement for represented RAW composition. No SAP or CCO is used here. -/

universe v w t
namespace CCO.RealHull.Geometry

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))

abbrev Atom := S.Atom () ()
abbrev FullColour := Option (Atom S)

def col (x y : M) : FullColour S := S.colour (i := ()) (j := ()) x y

theorem col_symm (x y : M) : col S x y = col S y x :=
  ParityHasse.Original.colour_symmetric S x y

@[simp] theorem col_none (x y : M) : col S x y = none ↔ x = y := by
  simpa only [col, S.colour_none_iff, Sigma.mk.injEq, heq_eq_eq, true_and]

theorem colour_realized (c : FullColour S) : ∃ x y : M, col S x y = c := by
  cases c with
  | none =>
    obtain ⟨x⟩ := S.nonemptySort ()
    exact ⟨x,x,(col_none S x x).mpr rfl⟩
  | some a => exact S.realized a

theorem col_some_of_ne {x y : M} (hne : x ≠ y) : ∃ a : Atom S, col S x y = some a := by
  cases hc : col S x y with
  | none => exact False.elim (hne ((col_none S x y).mp hc))
  | some a => exact ⟨a,rfl⟩

def prod (A B : Set (FullColour S)) : Set (FullColour S) :=
  {c | ∃ x y z : M, col S x y ∈ A ∧ col S y z ∈ B ∧ col S x z = c}

theorem prod_mono {A B A' B' : Set (FullColour S)}
    (hA : A ⊆ A') (hB : B ⊆ B') : prod S A B ⊆ prod S A' B' := by
  rintro c ⟨x,y,z,hxy,hyz,hxz⟩
  exact ⟨x,y,z,hA hxy,hB hyz,hxz⟩

theorem prod_comm (A B : Set (FullColour S)) : prod S A B = prod S B A := by
  ext c
  constructor <;> rintro ⟨x,y,z,hxy,hyz,hxz⟩ <;>
    exact ⟨z,y,x,(col_symm S z y) ▸ hyz,(col_symm S y x) ▸ hxy,
      (col_symm S z x).trans hxz⟩

@[simp] theorem prod_none_left (A : Set (FullColour S)) :
    prod S {none} A = A := by
  ext c
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    have he : x = y := (col_none S x y).mp (Set.mem_singleton_iff.mp hxy)
    subst y
    exact hxz ▸ hyz
  · intro hc
    obtain ⟨x,z,hxz⟩ := colour_realized S c
    exact ⟨x,x,z,(col_none S x x).mpr rfl,hxz.symm ▸ hc,hxz⟩

@[simp] theorem prod_none_right (A : Set (FullColour S)) :
    prod S A {none} = A := by rw [prod_comm, prod_none_left]

theorem none_mem_prod (A B : Set (FullColour S)) :
    none ∈ prod S A B ↔ (A ∩ B).Nonempty := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    have he := (col_none S x z).mp hxz
    subst z
    exact ⟨col S x y,hxy,(col_symm S x y) ▸ hyz⟩
  · rintro ⟨c,hA,hB⟩
    obtain ⟨x,y,hxy⟩ := colour_realized S c
    exact ⟨x,y,x,hxy.symm ▸ hA,(col_symm S y x).trans hxy ▸ hB,
      (col_none S x x).mpr rfl⟩

theorem optional_peirce (a b c : FullColour S) :
    c ∈ prod S {a} {b} ↔ a ∈ prod S {b} {c} := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    exact ⟨y,z,x,hyz,(col_symm S z x).trans hxz,
      (col_symm S y x).trans (Set.mem_singleton_iff.mp hxy)⟩
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    exact ⟨z,x,y,(col_symm S z x).trans hxz,hxy,
      (col_symm S z y).trans (Set.mem_singleton_iff.mp hyz)⟩

def row (a b : Atom S) : Set (Atom S) := {c | some c ∈ prod S {some a} {some b}}
def square (a : Atom S) : Set (Atom S) := row S a a

@[simp] theorem mem_row (a b c : Atom S) : c ∈ row S a b ↔ S.Triangle a b c := by
  constructor
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    exact ⟨x,y,z,Set.mem_singleton_iff.mp hxy,Set.mem_singleton_iff.mp hyz,hxz⟩
  · rintro ⟨x,y,z,hxy,hyz,hxz⟩
    exact ⟨x,y,z,hxy,hyz,hxz⟩

theorem row_symm (a b : Atom S) : row S a b = row S b a := by
  unfold row
  rw [prod_comm]

theorem row_peirce (a b c : Atom S) : c ∈ row S a b ↔ a ∈ row S b c :=
  optional_peirce S (some a) (some b) (some c)

variable {G : Type t} [Group G] [MulAction G M]
variable (H : HomogeneousSource S G)
include H

theorem col_invariant (g : G) (x y : M) : col S (g • x) (g • y) = col S x y :=
  S.colourInvariant_of_homogeneous H g x y

theorem prod_at_pair (A B : Set (FullColour S)) (x z : M) :
    col S x z ∈ prod S A B ↔ ∃ y, col S x y ∈ A ∧ col S y z ∈ B := by
  constructor
  · rintro ⟨x',y',z',hxy,hyz,hxz⟩
    obtain ⟨g,hgx,hgz⟩ := S.pair_homogeneous_of_homogeneous H x' x z' z hxz
    refine ⟨g • y',?_,?_⟩
    · have h := col_invariant S H g x' y'
      rw [hgx] at h
      exact h ▸ hxy
    · have h := col_invariant S H g y' z'
      rw [hgz] at h
      exact h ▸ hyz
  · rintro ⟨y,hxy,hyz⟩
    exact ⟨x,y,z,hxy,hyz,rfl⟩

theorem represented_prod (A B : Set (FullColour S)) :
    S.representedSupport (prod S A B) =
      TRel.comp (S.representedSupport A) (S.representedSupport B) := by
  funext x z
  exact propext (prod_at_pair S H A B x z)

omit H in
theorem represented_injective : Function.Injective
    (fun A : Set (FullColour S) => S.representedSupport (i := ()) (j := ()) A) := by
  intro A B hAB
  ext c
  obtain ⟨x,y,hxy⟩ := colour_realized S c
  have hh := congrFun (congrFun hAB x) y
  change (col S x y ∈ A) = (col S x y ∈ B) at hh
  exact hxy ▸ (Iff.of_eq hh)

theorem prod_assoc (A B C : Set (FullColour S)) :
    prod S (prod S A B) C = prod S A (prod S B C) := by
  apply represented_injective S
  simp only [represented_prod S H, TRel.comp_assoc]

theorem colour_serial (c : FullColour S) (x : M) : ∃ y, col S x y = c := by
  obtain ⟨a,b,hab⟩ := colour_realized S c
  obtain ⟨g,hga⟩ := S.original_sort_transitive_of_homogeneous H () a x
  exact ⟨g • b, (by rw [← hga]; exact (col_invariant S H g a b).trans hab)⟩

theorem prod_nonempty {A B : Set (FullColour S)}
    (hA : A.Nonempty) (hB : B.Nonempty) : (prod S A B).Nonempty := by
  obtain ⟨a,ha⟩ := hA
  obtain ⟨b,hb⟩ := hB
  obtain ⟨x,y,hxy⟩ := colour_realized S a
  obtain ⟨z,hyz⟩ := colour_serial S H b y
  exact ⟨col S x z,x,y,z,hxy.symm ▸ ha,hyz.symm ▸ hb,rfl⟩

end CCO.RealHull.Geometry
