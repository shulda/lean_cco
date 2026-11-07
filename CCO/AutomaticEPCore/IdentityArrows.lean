import CCO.AutomaticEPCore.FunctionalOriginal
import CCO.RigidGroupoid.Geometry.Bridge

/-! A FULL actual arrow over real identity is one original equivariant
permutation graph. This receives the actual phase-selected odd arrow,
without equating it to an unrelated GateChoice pivot. No SAP, infinite
source, marking or character hypothesis is required in this local fact. -/

universe u v w r
namespace CCO.AutomaticEPCore
open CCO.RigidGroupoid.Geometry

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type r} [Group G] [∀ i : ι, MulAction G (X i)]
variable (H : HomogeneousSource S G) {i : ι}
include H

/-- Both relational arrow equations concern ACTUAL identity classes.
Seriality and uniqueness construct the equivariant permutation itself. -/
theorem identity_arrow_functional
    (K : Kernel S i) (identityKernel : K.setoid = ⊥) (R : Arrow S K K) :
    ∃ h : OriginalFunctionalGroup G (X i),
      (∀ x y : X i, R.rel x y ↔ h.val x = y) ∧
      (R ≠ Arrow.id K → h ≠ 1) := by
  classical
  have serial := R.exact.serial S H
  let f : X i → X i := fun x => Classical.choose (serial x)
  have hf (x : X i) : R.rel x (f x) := Classical.choose_spec (serial x)
  have unique (x y z : X i) (hxy : R.rel x y) (hxz : R.rel x z) : y = z := by
    have hK : K.rel y z := by
      rw [← R.target]
      exact ⟨x,hxy,hxz⟩
    change K.setoid y z at hK
    rw [identityKernel] at hK
    exact hK
  have symmetric : ∀ x y, R.rel x y → R.rel y x := by
    intro x y hxy
    have hSym := R.exact.same_sort_converse S H
    exact Eq.mp (congrFun (congrFun hSym y) x) hxy
  have involutive : Function.Involutive f := by
    intro x
    exact unique (f x) (f (f x)) x (hf (f x)) (symmetric x (f x) (hf x))
  let e : Equiv.Perm (X i) :=
    { toFun := f
      invFun := f
      left_inv := involutive
      right_inv := involutive }
  let h : OriginalFunctionalGroup G (X i) :=
    ⟨e,by
      intro g x
      exact unique (g • x) (f (g • x)) (g • f x)
        (hf (g • x)) (R.exact.invariant S H g x (f x) (hf x))⟩
  have graph : ∀ x y : X i, R.rel x y ↔ h.val x = y := by
    intro x y
    constructor
    · exact unique x (f x) y (hf x)
    · intro he
      change f x = y at he
      exact he ▸ hf x
  refine ⟨h,graph,?_⟩
  intro hR hOne
  apply hR
  apply Arrow.ext
  funext x y
  apply propext
  have hValue : h.val x = x := congrArg (fun h : OriginalFunctionalGroup G (X i) => h.val x) hOne
  change R.rel x y ↔ K.setoid x y
  rw [identityKernel,graph,hValue]
  rfl

end CCO.AutomaticEPCore
