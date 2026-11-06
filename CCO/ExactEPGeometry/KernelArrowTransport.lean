import CCO.RigidGroupoid.Geometry.RootedGroupoid
import CCO.RigidGroupoid.Geometry.Transport

/-! Literal transport of whole source arrows across equal gate kernels.
Every relation is unchanged; no equivalence relation is weakened. -/

universe u v w
namespace CCO.ExactEPGeometry
open RigidGroupoid.Geometry

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {i j k : ι}

/-- Equality of the precise endpoint gates retypes the same full Arrow. -/
def kernelArrowEquiv {A A' : Kernel S i} {B B' : Kernel S j}
    (hA : A = A') (hB : B = B') : Arrow S A B ≃ Arrow S A' B' := by
  subst A'
  subst B'
  exact Equiv.refl _

theorem kernelArrowEquiv_id {A A' : Kernel S i} (hA : A = A') :
    kernelArrowEquiv hA hA (Arrow.id A) = Arrow.id A' := by
  subst A'
  rfl

theorem kernelArrowEquiv_comp (C : ExactCalculus S)
    {A A' : Kernel S i} {B B' : Kernel S j} {D D' : Kernel S k}
    (hA : A = A') (hB : B = B') (hD : D = D')
    (R : Arrow S A B) (T : Arrow S B D) :
    kernelArrowEquiv hA hD (R.comp C T) =
      (kernelArrowEquiv hA hB R).comp C (kernelArrowEquiv hB hD T) := by
  subst A'
  subst B'
  subst D'
  rfl

theorem kernelArrowEquiv_rel {A A' : Kernel S i} {B B' : Kernel S j}
    (hA : A = A') (hB : B = B') (R : Arrow S A B) :
    (kernelArrowEquiv hA hB R).rel = R.rel := by
  subst A'
  subst B'
  rfl

theorem kernelArrowEquiv_dominant {A A' : Kernel S i}
    (hA : A = A') (R : Arrow S A A) (hR : Dominant A R) :
    Dominant A' (kernelArrowEquiv hA hA R) := by
  subst A'
  exact hR

end CCO.ExactEPGeometry
