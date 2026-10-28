import CCO.RigidGroupoid.Geometry.PointAction

/-! C31's actual source-orbital bridge.  Rigid graphs are precisely the
actual ORIGINAL ambient-action orbitals whose endpoints share a rigid
groupoid orbit. This makes no quotient homogeneity claim. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G)
variable {i j : ι} {A : Kernel S i} {B : Kernel S j}

theorem orbital_eq_rigid_graph (R : Arrow S A B) (q : A.Class) :
    letI := A.action H
    letI := B.action H
    GroupActions.orbital (G := G) q (R.quotientMap H q) =
      (fun a b => R.quotientMap H a = b) := by
  letI := A.action H
  letI := B.action H
  induction q using Quotient.inductionOn with
  | _ x =>
    exact (R.quotient_graph_orbital H (R.pointImage_spec H x)).symm

theorem rigid_orbital_iff (q : A.Class) (r : B.Class) :
    letI := A.action H
    letI := B.action H
    (∃ R : Arrow S A B, R.quotientMap H q = r) ↔
      ∃ R : Arrow S A B, GroupActions.orbital (G := G) q r =
        (fun a b => R.quotientMap H a = b) := by
  letI := A.action H
  letI := B.action H
  constructor
  · rintro ⟨R,rfl⟩
    exact ⟨R,orbital_eq_rigid_graph S H R q⟩
  · rintro ⟨R,hR⟩
    refine ⟨R,?_⟩
    have h := GroupActions.orbital_nonempty (G := G) q r
    rw [hR] at h
    exact h

theorem nonrigid_different_orbits (q : A.Class) (r : B.Class)
    (h : letI := A.action H; letI := B.action H
      ∀ R : Arrow S A B, GroupActions.orbital (G := G) q r ≠
        (fun a b => R.quotientMap H a = b)) :
    ¬ ∃ R : Arrow S A B, R.quotientMap H q = r := by
  intro ht
  obtain ⟨R,hR⟩ := (rigid_orbital_iff S H q r).mp ht
  exact h R hR

end CCO.RigidGroupoid.Phase
