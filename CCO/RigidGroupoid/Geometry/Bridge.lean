import CCO.RigidGroupoid.Geometry.Basic
import Mathlib.Data.Setoid.Basic

/-! Exact bridges are rectangular represented relations. Their actual target
kernel and BOTH bridge identities are proved before any quotient function is
constructed. The real relation is not asserted single-valued. -/

universe u v w t
namespace CCO.RigidGroupoid.Geometry
variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)

structure Kernel (i : ι) where
  setoid : Setoid (X i)
  exact : FullExact S setoid.r

namespace Kernel
variable {S} {i : ι} (A : Kernel S i)
abbrev rel : TRel X i i := A.setoid.r

theorem comp_self : TRel.comp A.rel A.rel = A.rel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    exact A.setoid.trans hxz hzy
  · intro hxy
    exact ⟨y,hxy,A.setoid.refl y⟩

theorem converse : TRel.converse A.rel = A.rel := by
  funext x y
  exact propext ⟨A.setoid.symm,A.setoid.symm⟩

theorem left_absorb {B : Kernel S i} (h : A.setoid ≤ B.setoid) :
    TRel.comp A.rel B.rel = B.rel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    exact B.setoid.trans (h hxz) hzy
  · intro hxy
    exact ⟨x,A.setoid.refl x,hxy⟩

theorem right_absorb {B : Kernel S i} (h : A.setoid ≤ B.setoid) :
    TRel.comp B.rel A.rel = B.rel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨z,hxz,hzy⟩
    exact B.setoid.trans hxz (h hzy)
  · intro hxy
    exact ⟨y,hxy,A.setoid.refl y⟩
end Kernel

structure Bridge {i : ι} (A : Kernel S i) (j : ι) where
  rel : TRel X i j
  exact : FullExact S rel
  left : TRel.comp A.rel rel = rel
  source : TRel.comp rel (TRel.converse rel) = A.rel

structure Arrow {i j : ι} (A : Kernel S i) (B : Kernel S j) where
  rel : TRel X i j
  exact : FullExact S rel
  left : TRel.comp A.rel rel = rel
  right : TRel.comp rel B.rel = rel
  source : TRel.comp rel (TRel.converse rel) = A.rel
  target : TRel.comp (TRel.converse rel) rel = B.rel

namespace Bridge
variable {S} {i j : ι} {A : Kernel S i} (R : Bridge S A j)

theorem right : TRel.comp R.rel (TRel.comp (TRel.converse R.rel) R.rel) = R.rel := by
  rw [← TRel.comp_assoc,R.source,R.left]

variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)

def targetKernel : Kernel S j where
  setoid := {
    r := TRel.comp (TRel.converse R.rel) R.rel
    iseqv := ⟨by
      intro y
      obtain ⟨x,hxy⟩ := R.exact.coserial S H y
      exact ⟨x,hxy,hxy⟩,
      by rintro y z ⟨x,hxy,hxz⟩; exact ⟨x,hxz,hxy⟩,
      by
        rintro y z t ⟨x,hxy,hxz⟩ ⟨x',hx'z,hx't⟩
        have hK : A.rel x x' := by
          rw [← R.source]
          exact ⟨z,hxz,hx'z⟩
        have hxt : R.rel x t := by
          rw [← R.left]
          exact ⟨x',hK,hx't⟩
        exact ⟨x,hxy,hxt⟩⟩
  }
  exact := C.comp (fullExact_converse S R.exact) R.exact

def toArrow : Arrow S A (R.targetKernel H C) where
  rel := R.rel
  exact := R.exact
  left := R.left
  right := R.right
  source := R.source
  target := rfl
end Bridge

namespace Arrow
variable {S} {i j k l : ι} {A : Kernel S i} {B : Kernel S j}
variable {D : Kernel S k} {E : Kernel S l}

@[ext] theorem ext {R T : Arrow S A B} (h : R.rel = T.rel) : R = T := by
  cases R
  cases T
  cases h
  rfl

def toBridge (R : Arrow S A B) : Bridge S A j :=
  ⟨R.rel,R.exact,R.left,R.source⟩

def id (A : Kernel S i) : Arrow S A A where
  rel := A.rel
  exact := A.exact
  left := A.comp_self
  right := A.comp_self
  source := by rw [A.converse,A.comp_self]
  target := by rw [A.converse,A.comp_self]

def inv (R : Arrow S A B) : Arrow S B A where
  rel := TRel.converse R.rel
  exact := fullExact_converse S R.exact
  left := by
    have h := congrArg TRel.converse R.right
    simpa only [TRel.converse_comp,B.converse] using h
  right := by
    have h := congrArg TRel.converse R.left
    simpa only [TRel.converse_comp,A.converse] using h
  source := by simpa only [TRel.converse_converse] using R.target
  target := by simpa only [TRel.converse_converse] using R.source

def comp (C : ExactCalculus S) (R : Arrow S A B) (T : Arrow S B D) : Arrow S A D where
  rel := TRel.comp R.rel T.rel
  exact := C.comp R.exact T.exact
  left := by rw [← TRel.comp_assoc,R.left]
  right := by rw [TRel.comp_assoc,T.right]
  source := by
    rw [TRel.converse_comp]
    calc
      TRel.comp (TRel.comp R.rel T.rel) (TRel.comp (TRel.converse T.rel) (TRel.converse R.rel)) =
          TRel.comp R.rel (TRel.comp (TRel.comp T.rel (TRel.converse T.rel)) (TRel.converse R.rel)) := by
        simp only [TRel.comp_assoc]
      _ = A.rel := by rw [T.source,← TRel.comp_assoc,R.right,R.source]
  target := by
    rw [TRel.converse_comp]
    calc
      TRel.comp (TRel.comp (TRel.converse T.rel) (TRel.converse R.rel)) (TRel.comp R.rel T.rel) =
          TRel.comp (TRel.converse T.rel) (TRel.comp (TRel.comp (TRel.converse R.rel) R.rel) T.rel) := by
        simp only [TRel.comp_assoc]
      _ = D.rel := by rw [R.target,T.left,T.target]

@[simp] theorem id_comp (C : ExactCalculus S) (R : Arrow S A B) : (id A).comp C R = R :=
  ext R.left

@[simp] theorem comp_id (C : ExactCalculus S) (R : Arrow S A B) : R.comp C (id B) = R :=
  ext R.right

theorem comp_assoc (C : ExactCalculus S) (R : Arrow S A B) (T : Arrow S B D) (U : Arrow S D E) :
    (R.comp C T).comp C U = R.comp C (T.comp C U) :=
  ext (TRel.comp_assoc R.rel T.rel U.rel)

@[simp] theorem comp_inv (C : ExactCalculus S) (R : Arrow S A B) : R.comp C R.inv = id A :=
  ext R.source

@[simp] theorem inv_comp (C : ExactCalculus S) (R : Arrow S A B) : R.inv.comp C R = id B :=
  ext R.target

@[simp] theorem inv_inv (R : Arrow S A B) : R.inv.inv = R := ext rfl

theorem comp_injective_right (C : ExactCalculus S) (R : Arrow S A B) :
    Function.Injective (fun T : Arrow S B D => R.comp C T) := by
  intro T U h
  have hh := congrArg (fun V => R.inv.comp C V) h
  simpa only [← comp_assoc,inv_comp,id_comp] using hh

theorem comp_injective_left (C : ExactCalculus S) (T : Arrow S B D) :
    Function.Injective (fun R : Arrow S A B => R.comp C T) := by
  intro R U h
  have hh := congrArg (fun V => V.comp C T.inv) h
  simpa only [comp_assoc,comp_inv,comp_id] using hh

end Arrow
end CCO.RigidGroupoid.Geometry
