import CCO.RigidGroupoid.Phase.RigidSupport

/-! Literal represented subgroup unions. Their equivalence laws are
elementary; exactness is retained as a separate hypothesis until the actual
slice square supplies it. No arbitrary subgroup is declared exact. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {i j : ι} {A : Kernel S i} {B : Kernel S j}

def isotropyUnion (U : Subgroup (Isotropy S C B)) : TRel X j j :=
  fun x y => ∃ h, h ∈ U ∧ h.rel x y

theorem shifted_converse_product (d : Arrow S A B) (h k : Isotropy S C B) :
    TRel.comp (TRel.converse (d.comp C h).rel) (d.comp C k).rel =
      TRel.comp (TRel.converse h.rel) k.rel := by
  change TRel.comp (TRel.converse (TRel.comp d.rel h.rel))
    (TRel.comp d.rel k.rel) = _
  rw [TRel.converse_comp]
  calc
    TRel.comp (TRel.comp (TRel.converse h.rel) (TRel.converse d.rel))
        (TRel.comp d.rel k.rel) =
      TRel.comp (TRel.converse h.rel)
        (TRel.comp (TRel.comp (TRel.converse d.rel) d.rel) k.rel) := by
          simp only [TRel.comp_assoc]
    _ = _ := by rw [d.target,k.left]

include H
theorem representedSlice_square (d : Arrow S A B) (U : Subgroup (Isotropy S C B)) :
    TRel.comp (TRel.converse (representedSlice S C d (U : Set (Isotropy S C B))))
      (representedSlice S C d (U : Set (Isotropy S C B))) = isotropyUnion S C U := by
  funext x y
  apply propext
  constructor
  · rintro ⟨a,⟨h,hh,hax⟩,k,hk,hay⟩
    refine ⟨h⁻¹*k,U.mul_mem (U.inv_mem hh) hk,?_⟩
    change TRel.comp (TRel.converse h.rel) k.rel x y
    rw [← shifted_converse_product S C d h k]
    exact ⟨a,hax,hay⟩
  · rintro ⟨h,hh,hxy⟩
    obtain ⟨a,hax⟩ := d.exact.coserial S H x
    refine ⟨a,?_,?_⟩
    · exact ⟨1,U.one_mem,x,hax,B.setoid.refl x⟩
    · exact ⟨h,hh,x,hax,hxy⟩

def isotropyKernel (U : Subgroup (Isotropy S C B))
    (hU : FullExact S (isotropyUnion S C U)) : Kernel S j where
  setoid := {
    r := isotropyUnion S C U
    iseqv := ⟨by
      intro x
      exact ⟨1,U.one_mem,B.setoid.refl x⟩,
      by
        rintro x y ⟨h,hh,hxy⟩
        exact ⟨h⁻¹,U.inv_mem hh,hxy⟩,
      by
        rintro x y z ⟨h,hh,hxy⟩ ⟨k,hk,hyz⟩
        exact ⟨h*k,U.mul_mem hh hk,y,hxy,hyz⟩⟩
  }
  exact := hU

theorem isotropyKernel_contains_gate (U : Subgroup (Isotropy S C B))
    (hU : FullExact S (isotropyUnion S C U)) :
    ∀ x y, B.rel x y → (isotropyKernel S C U hU).rel x y := by
  intro x y hxy
  exact ⟨1,U.one_mem,hxy⟩

end CCO.RigidGroupoid.Phase
