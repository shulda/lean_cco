import CCO.RigidGroupoid.Phase.AffineSlice
import CCO.RigidGroupoid.Phase.Factorisation

/-! Actual C20–C23 consumers. The reference arrow is CHOSEN from the
nonempty source slice, and its exact represented subgroup kernel is BUILT.
The trivial subgroup boundary gives the original rectangular arrow. -/

universe u v w t
namespace CCO.RigidGroupoid.Phase
open Geometry

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i, MulAction G (X i)]
variable (H : HomogeneousSource S G) (C : ExactCalculus S)
variable {i j : ι} {A : Kernel S i} {B : Kernel S j}

include H
theorem actual_exact_rigid_slice (cco : SemanticCCO.{u,v,max u v,w} S)
    {D : TRel X i j} (hD : FullExact S D)
    (hLeft : TRel.comp A.rel D = D) (hRight : TRel.comp D B.rel = D)
    (hCovered : ∀ x y, D x y → ∃ T : Arrow S A B, T.rel x y) :
    ∃ (d : Arrow S A B) (U : Subgroup (Isotropy S C B)) (K : Kernel S j),
      D = representedSlice S C d (U : Set (Isotropy S C B)) ∧
      TRel.comp (TRel.converse D) D = K.rel ∧
      K.rel = isotropyUnion S C U ∧
      (∀ x y, B.rel x y → K.rel x y) := by
  obtain ⟨x,y,hxy⟩ := hD.nonempty S
  obtain ⟨d,_⟩ := hCovered x y hxy
  obtain ⟨d',U,hRep,hSquare,hU⟩ := exact_rigid_coset S H C cco d hD hLeft hRight hCovered
  exact ⟨d',U,isotropyKernel S C U hU,hRep,hSquare,rfl,
    isotropyKernel_contains_gate S H C U hU⟩

theorem trivial_coset (d : Arrow S A B) :
    representedSlice S C d (⊥ : Subgroup (Isotropy S C B)) = d.rel := by
  funext x y
  apply propext
  constructor
  · rintro ⟨h,hh,hxy⟩
    have he : h = 1 := hh
    subst h
    exact Eq.mp (congrFun (congrFun d.right x) y) hxy
  · intro hxy
    exact ⟨1,(⊥ : Subgroup (Isotropy S C B)).one_mem,y,hxy,B.setoid.refl y⟩

/-- In particular the one-arrow slice at an object is its actual gate,
which may contain many real point pairs and is not silently real equality. -/
theorem identity_trivial_coset (A : Kernel S i) :
    representedSlice S C (Arrow.id A) (⊥ : Subgroup (Isotropy S C A)) = A.rel :=
  trivial_coset S H C (Arrow.id A)

end CCO.RigidGroupoid.Phase
