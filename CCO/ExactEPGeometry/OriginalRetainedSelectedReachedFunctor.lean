import CCO.ExactEPGeometry.OriginalRetainedSelectedReachedEquiv
import CCO.ExactEPGeometry.KernelArrowTransport
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# B062 C103: the entire actual retained selected groupoid

The actual Reached bijection carries every FULL Hom by equality of the
precise true endpoint kernels. This is a fully faithful actual functor,
with the previously proved literal object bijection, not a selected
generating-arrow map or a hypothetical source equivalence provider.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter.Towers RigidGroupoid.Geometry CategoryTheory
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- The complete actual occupancy groupoid maps to the FULL actual
selected Reached groupoid, preserving each relation literally. -/
def originalRetainedSelectedReachedFunctor :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
    letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
    OriginalReachedOccupancy A B P base hBase E Kroot ⥤ Reached Q.source KQ := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
  let f := originalRetainedOccupancyToSelectedReached A B P transport tp hOne Kroot E hE
  let hk := originalRetainedSelectedReached_kernel A B P transport tp hOne Kroot E hE
  exact {
    obj := f
    map := fun {a b} R => kernelArrowEquiv (hk a).symm (hk b).symm R
    map_id := fun a => kernelArrowEquiv_id (hk a).symm
    map_comp := fun {a b c} R T =>
      kernelArrowEquiv_comp CQ (hk a).symm (hk b).symm (hk c).symm R T
  }

/-- Every actual target Hom has a unique preimage: the endpoint gate
equalities are literal equivalences of the whole Arrow types. -/
def originalRetainedSelectedReachedFullyFaithful :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
    letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
    (originalRetainedSelectedReachedFunctor A B P transport tp hOne Kroot E hE).FullyFaithful := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let CQ := exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
  letI := Reached.groupoid Q.homogeneous CQ (A := KQ)
  let hk := originalRetainedSelectedReached_kernel A B P transport tp hOne Kroot E hE
  exact {
    preimage := fun {a b} R => (kernelArrowEquiv (hk a).symm (hk b).symm).symm R
    map_preimage := fun {a b} R => (kernelArrowEquiv (hk a).symm (hk b).symm).apply_symm_apply R
    preimage_map := fun {a b} R => (kernelArrowEquiv (hk a).symm (hk b).symm).symm_apply_apply R
  }

end
end CCO.ExactEPGeometry
