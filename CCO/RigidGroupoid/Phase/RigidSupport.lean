import CCO.RigidGroupoid.Geometry.PointAction

/-! C20: an invariant saturated slice supported on actual rigid arrows is
a union of WHOLE arrows. Coefficients are the actual target isotropy, not
an assumed abstract orbital palette. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {i j : ι} {A : Kernel S i} {B : Kernel S j}

include H
theorem whole_arrow_of_meets (T : Arrow S A B) {D : TRel X i j}
    (hInv : TRel.Invariant (G := G) D) (hRight : TRel.comp D B.rel = D)
    {x : X i} {y : X j} (hT : T.rel x y) (hD : D x y) :
    ∀ a b, T.rel a b → D a b := by
  intro a b hab
  obtain ⟨g,hgx⟩ := S.original_sort_transitive_of_homogeneous H i x a
  have hgT : T.rel a (g • y) := by
    simpa only [hgx] using T.exact.invariant S H g x y hT
  have hgD : D a (g • y) := by simpa only [hgx] using hInv g x y hD
  have hB : B.rel (g • y) b := by
    rw [← T.target]
    exact ⟨a,hgT,hab⟩
  rw [← hRight]
  exact ⟨g • y,hgD,hB⟩

def rigidSupport (d : Arrow S A B) (D : TRel X i j) : Set (Isotropy S C B) :=
  {h | ∀ x y, (d.comp C h).rel x y → D x y}

def representedSlice (d : Arrow S A B) (E : Set (Isotropy S C B)) : TRel X i j :=
  fun x y => ∃ h, h ∈ E ∧ (d.comp C h).rel x y

theorem whole_rigid_support (d : Arrow S A B) {D : TRel X i j}
    (hInv : TRel.Invariant (G := G) D) (hRight : TRel.comp D B.rel = D)
    (hCovered : ∀ x y, D x y → ∃ T : Arrow S A B, T.rel x y) :
    D = representedSlice S C d (rigidSupport S C d D) := by
  funext x y
  apply propext
  constructor
  · intro hD
    obtain ⟨T,hT⟩ := hCovered x y hD
    obtain ⟨h,hh,_⟩ := Arrow.target_torsor C T d
    refine ⟨h,?_,?_⟩
    · intro a b hab
      rw [hh] at hab
      exact whole_arrow_of_meets S H T hInv hRight hT hD a b hab
    · rw [hh]
      exact hT
  · rintro ⟨h,hh,hxy⟩
    exact hh x y hxy

theorem rigidSupport_nonempty (d : Arrow S A B) {D : TRel X i j}
    (hD : FullExact S D) (hRight : TRel.comp D B.rel = D)
    (hCovered : ∀ x y, D x y → ∃ T : Arrow S A B, T.rel x y) :
    (rigidSupport S C d D).Nonempty := by
  obtain ⟨x,y,hxy⟩ := hD.nonempty S
  rw [whole_rigid_support S H C d (hD.invariant S H) hRight hCovered] at hxy
  obtain ⟨h,hh,_⟩ := hxy
  exact ⟨h,hh⟩

theorem coefficient_unique (d : Arrow S A B) {h k : Isotropy S C B}
    {x : X i} {y : X j} (hh : (d.comp C h).rel x y)
    (hk : (d.comp C k).rel x y) : h = k :=
  Arrow.comp_injective_right C d
    ((d.comp C h).eq_of_common_real_pair H (d.comp C k) hh hk)

def rightTranslate (E : Set (Isotropy S C B)) (v : Isotropy S C B) :
    Set (Isotropy S C B) := {h | ∃ a, a ∈ E ∧ a * v = h}

theorem slice_comp_isotropy (d : Arrow S A B) (E : Set (Isotropy S C B))
    (v : Isotropy S C B) :
    TRel.comp (representedSlice S C d E) v.rel =
      representedSlice S C d (rightTranslate S C E v) := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,⟨a,ha,haz⟩,hzy⟩
    refine ⟨a*v,⟨a,ha,rfl⟩,?_⟩
    change TRel.comp d.rel (TRel.comp a.rel v.rel) x y
    rw [← TRel.comp_assoc]
    exact ⟨z,haz,hzy⟩
  · rintro ⟨h,⟨a,ha,rfl⟩,hxy⟩
    change TRel.comp d.rel (TRel.comp a.rel v.rel) x y at hxy
    rw [← TRel.comp_assoc] at hxy
    obtain ⟨z,haz,hzy⟩ := hxy
    exact ⟨z,⟨a,ha,haz⟩,hzy⟩

end CCO.RigidGroupoid.Phase
