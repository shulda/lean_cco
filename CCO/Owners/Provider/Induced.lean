import CCO.Owners.Product.SparseDescent
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Sigma
import Mathlib.Basic.Finite.Sigma
import Mathlib.Basic.Finite.Prod

/-! Actual finite induced quotient homomorphisms and restrictions (C01).
The orbital language is the complete original language, not a replacement
with freely chosen quotient colours. -/
namespace CCO.Owners.Provider
open Product

variable {G A O : Type*} [Group G] [MulAction G A] [MulAction G O]

/-- The literal projection between two displayed induced subsets. -/
def ownerProjection (π : A → O) (D : Set A) (B : Set O)
    (hD : ∀ x : D, π x.val ∈ B) : D → B :=
  fun x => ⟨π x.val, hD x⟩

/-- All source automorphisms descend through the actual recognized
quotient. `OrbitalQuotient.action` then gives its honest homomorphism;
its `projectedPartial` gives sparse-domain descent and reflection. -/
def inducedQuotient (π : A → O)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (D : Set A) (B : Set O) (hD : ∀ x : D, π x.val ∈ B)
    (onto : Function.Surjective (ownerProjection π D B hD)) :
    OrbitalQuotient (G := G) (Subtype.val : D → A) (Subtype.val : B → O) where
  ambient := π
  equivariant := equivπ
  projection := ownerProjection π D B hD
  surjective := onto
  target_injective := Subtype.val_injective
  commutes _ := rfl

theorem induced_owner_unique (π : A → O)
    (equivπ : ∀ (g : G) x, π (g • x) = g • π x)
    (D : Set A) (B : Set O) (hD : ∀ x : D, π x.val ∈ B)
    (onto : Function.Surjective (ownerProjection π D B hD))
    (g : OrbitalAut G A (Subtype.val : D → A))
    (γ : OrbitalAut G O (Subtype.val : B → O))
    (hγ : ∀ x : D, γ.val (ownerProjection π D B hD x) =
      ownerProjection π D B hD (g.val x)) :
    (inducedQuotient π equivπ D B hD onto).action g = γ := by
  apply Subtype.ext
  apply Equiv.ext
  intro b
  obtain ⟨x,rfl⟩ := onto b
  exact ((inducedQuotient π equivπ D B hD onto).action_projection g x).trans
    (hγ x).symm

/-- Restrict a full induced automorphism to a finite invariant subset.
Only forward invariance is needed: finite injection supplies onto. -/
noncomputable def restrictAut {U : Type*} {ι : U → A}
    (g : OrbitalAut G A ι) (D : Set U) [Finite D]
    (hD : ∀ x : D, g.val x.val ∈ D) :
    OrbitalAut G A (fun x : D => ι x.val) := by
  let f : D → D := fun x => ⟨g.val x.val,hD x⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    exact g.val.injective (congrArg Subtype.val h)
  let e : Equiv.Perm D := Equiv.ofBijective f
    ⟨hi, Finite.surjective_of_injective hi⟩
  exact ⟨e,(mem_orbitalAut_iff e).mpr (fun x y => orbitalAut_pair g x.val y.val)⟩

@[simp] theorem restrictAut_apply {U : Type*} {ι : U → A}
    (g : OrbitalAut G A ι) (D : Set U) [Finite D]
    (hD : ∀ x : D, g.val x.val ∈ D) (x : D) :
    ((restrictAut g D hD).val x).val = g.val x.val := rfl

/-- The same restriction on literal ambient induced subsets. -/
noncomputable def restrictInducedAut {C D : Set A} [Finite D]
    (g : OrbitalAut G A (Subtype.val : C → A)) (hDC : D ⊆ C)
    (hD : ∀ x : D, (g.val ⟨x.val,hDC x.property⟩).val ∈ D) :
    OrbitalAut G A (Subtype.val : D → A) := by
  let f : D → D := fun x => ⟨(g.val ⟨x.val,hDC x.property⟩).val,hD x⟩
  have hi : Function.Injective f := by
    intro x y h
    apply Subtype.ext
    have hv : (g.val ⟨x.val,hDC x.property⟩).val =
        (g.val ⟨y.val,hDC y.property⟩).val := congrArg (fun z : D => z.val) h
    have hh := g.val.injective (Subtype.ext hv)
    exact congrArg (fun z : C => z.val) hh
  let e : Equiv.Perm D := Equiv.ofBijective f
    ⟨hi,Finite.surjective_of_injective hi⟩
  exact ⟨e,(mem_orbitalAut_iff e).mpr (fun x y =>
    orbitalAut_pair g ⟨x.val,hDC x.property⟩ ⟨y.val,hDC y.property⟩)⟩

@[simp] theorem restrictInducedAut_apply {C D : Set A} [Finite D]
    (g : OrbitalAut G A (Subtype.val : C → A)) (hDC : D ⊆ C)
    (hD : ∀ x : D, (g.val ⟨x.val,hDC x.property⟩).val ∈ D) (x : D) :
    ((restrictInducedAut g hDC hD).val x).val =
      (g.val ⟨x.val,hDC x.property⟩).val := rfl

/-- All partial maps of a finite carrier form a finite type, including
the empty partial map. No finite list of singleton requests is omitted. -/
instance finite_orbitalPartial {U : Type*} [Finite U] (ι : U → A) :
    Finite (OrbitalPartial (G := G) ι) := by
  let f : OrbitalPartial (G := G) ι → Σ d : Set U, d → U :=
    fun p => ⟨p.domain,p.map⟩
  apply Finite.of_injective f
  intro p q hpq
  cases p
  cases q
  cases hpq
  rfl

end CCO.Owners.Provider
