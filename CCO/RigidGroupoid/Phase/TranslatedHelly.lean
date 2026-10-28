import CCO.RigidGroupoid.Phase.RigidSupport
import CCO.RigidGroupoid.Phase.ExactFamilyHelly

/-! The affine coefficient Helly premise is DISCHARGED by old exact menus.
Intersections are first interpreted as actual old relation intersections;
freeness then reads their common pair as ONE common arrow coefficient. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {i j : ι} {A : Kernel S i} {B : Kernel S j}

include H
theorem mem_rightTranslate_iff (E : Set (Isotropy S C B))
    (h v : Isotropy S C B) :
    h ∈ rightTranslate S C E v ↔ h*v ∈ E := by
  constructor
  · rintro ⟨a,ha,rfl⟩
    simpa only [mul_assoc,Isotropy.square_one C B H,mul_one] using ha
  · intro hhv
    refine ⟨h*v,hhv,?_⟩
    rw [mul_assoc,Isotropy.square_one C B H,mul_one]

theorem actual_support_translate_helly
    (cco : SemanticCCO.{u,v,max u v,w} S) (d : Arrow S A B)
    {D : TRel X i j} (hD : FullExact S D) (hRight : TRel.comp D B.rel = D)
    (hCovered : ∀ x y, D x y → ∃ T : Arrow S A B, T.rel x y)
    (F : Finset (Isotropy S C B))
    (hPair : ∀ a ∈ F, ∀ b ∈ F, ∃ z : Isotropy S C B,
      z*a ∈ rigidSupport S C d D ∧ z*b ∈ rigidSupport S C d D) :
    ∃ z : Isotropy S C B, ∀ a ∈ F, z*a ∈ rigidSupport S C d D := by
  classical
  by_cases hF : F.Nonempty
  · let E := rigidSupport S C d D
    let R (a : F) : TRel X i j := TRel.comp D a.val.rel
    have hRep (a : F) : R a = representedSlice S C d (rightTranslate S C E a.val) := by
      dsimp only [R]
      rw [whole_rigid_support S H C d (hD.invariant S H) hRight hCovered]
      exact slice_comp_isotropy S H C d E a.val
    have hR (a : F) : FullExact S (R a) := C.comp hD a.val.exact
    have hp (a b : F) : TRel.Nonempty (fun x y => R a x y ∧ R b x y) := by
      obtain ⟨z,hza,hzb⟩ := hPair a.val a.property b.val b.property
      obtain ⟨x,y,hxy⟩ := (d.comp C z).exact.nonempty S
      refine ⟨x,y,?_,?_⟩
      · rw [hRep]
        exact ⟨z,(mem_rightTranslate_iff S H C E z a.val).mpr hza,hxy⟩
      · rw [hRep]
        exact ⟨z,(mem_rightTranslate_iff S H C E z b.val).mpr hzb,hxy⟩
    obtain ⟨x,y,hxy⟩ := fullExact_family_helly S H cco R hR hp
    obtain ⟨a,ha⟩ := hF
    have hfirst := hxy ⟨a,ha⟩
    rw [hRep] at hfirst
    obtain ⟨z,hz,hzxy⟩ := hfirst
    refine ⟨z,?_⟩
    intro b hb
    have hnext := hxy ⟨b,hb⟩
    rw [hRep] at hnext
    obtain ⟨z',hz',hz'xy⟩ := hnext
    have he : z' = z := coefficient_unique S H C d hz'xy hzxy
    subst z'
    exact (mem_rightTranslate_iff S H C E z b).mp hz'
  · refine ⟨1,?_⟩
    intro a ha
    exact (hF ⟨a,ha⟩).elim

end CCO.RigidGroupoid.Phase
