import CCO.ExactEPGeometry.OriginalRetainedSelectedReachedFunctor
import CCO.ExactEPGeometry.CharacterObjectTransport
import CCO.ExactEPGeometry.OriginalRetainedSelectedOccupancyCharacter

/-!
# B062 C103: corrected character on the FULL actual selected source

All actually reached source objects, every true reached gate and all full
Hom arrows have now been identified. The resulting character is on precisely
the SourcePhase object type. Its values on EVERY previous occupancy-arrow
are proved equal to the original corrected character. The inverse uses only
equality arrows, so no arbitrary connector changes the object gauge.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter APCharacter.Towers RigidGroupoid.Geometry
open RigidGroupoid.Phase CategoryTheory
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- The actual selected source has the corrected FULL reached character,
with all source/Reached/Hom providers constructed internally. -/
def originalRetainedActualSelectedCharacter :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    Character Q.source Q.homogeneous CQ KQ := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
  let F := originalRetainedSelectedReachedFunctor A B P transport tp hOne Kroot E hE
  let FF := originalRetainedSelectedReachedFullyFaithful A B P transport tp hOne Kroot E hE
  let e := originalRetainedOccupancySelectedReachedEquiv A B P transport tp hOne Kroot E hE
  exact characterFunctorPullback (strictObjectInverse F FF e (fun _ => rfl))
    (originalRetainedSelectedOccupancyCharacter A B P transport tp hOne Kroot phase E hE)

include tp hE in
/-- Exact all-Hom readout: this is the existing corrected character on
each whole original occupancy-arrow, not just agreement on odd loops. -/
theorem originalRetainedActualSelectedCharacter_value :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
    letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
    ∀ {a b : OriginalReachedOccupancy A B P base hBase E Kroot} (R : a ⟶ b),
      (originalRetainedActualSelectedCharacter A B P transport tp hOne Kroot phase E hE).value
        ((originalRetainedSelectedReachedFunctor A B P transport tp hOne Kroot E hE).map R) =
      (originalRetainedSelectedOccupancyCharacter A B P transport tp hOne Kroot phase E hE).value R := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
  dsimp only
  intro a b R
  exact characterStrictTransport_map
    (originalRetainedSelectedReachedFunctor A B P transport tp hOne Kroot E hE)
    (originalRetainedSelectedReachedFullyFaithful A B P transport tp hOne Kroot E hE)
    (originalRetainedOccupancySelectedReachedEquiv A B P transport tp hOne Kroot E hE)
    (fun _ => rfl)
    (originalRetainedSelectedOccupancyCharacter A B P transport tp hOne Kroot phase E hE) R

end
end CCO.ExactEPGeometry
