import CCO.ExactEPGeometry.OriginalReachedGlobalGauge
import CCO.ExactEPGeometry.OriginalRetainedSelectedGroupoid

/-!
# B062 C84: the actual occupancy-object quotient of the retained groupoid

The actual FULL Reached groupoid has a finite object set. The true
original E-support is a setoid on its ACTUAL reached objects, with
a genuine reached anchor in every class. At each such anchor, C82/C83
constructs the real selected-quotient full-RAW-exact projected gate.
The homs between two anchor gates are ALL complete Arrow values of
the actual selected-quotient CurrentSource.

These full Hom sets and the proven selected AP+HOM CCO exact calculus
form an honest finite connected GROUPOID with precisely one object
for every original E-occupancy component of the FULL reached set.
This construction does not postulate a quotient group section, SAP,
exactness under arbitrary sort deletion, an artificial groupoid action
or a chosen generator in place of complete Hom sets.

The subsequent character descent and masks must be certified
separately; merely constructing this full groupoid does not prove
their source properties.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry
open CategoryTheory

noncomputable section

/-- The object index for the actual selected retained groupoid is
FINITE: it is a quotient of the finite genuinely Reached source
object family, not a new hypothetical quotient sort set. -/
theorem originalReachedOccupancyFinite
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r) :
    Finite (OriginalReachedOccupancy A B P base hOne E Kroot) := by
  letI : Finite (Reached B.source Kroot) := inferInstance
  exact Finite.of_surjective
    (fun b : Reached B.source Kroot =>
      (Quotient.mk'' b :
        OriginalReachedOccupancy A B P base hOne E Kroot))
    Quotient.mk''_surjective

/-- C84 actual selected occupancy-skeleton GROUPOID. Objects are
literal E-occupancy equivalence classes of all source Reached
objects; each is represented by an actual reached anchor. The
kernels are the genuine projected source K_b/E_b on that chosen
object, and every Hom is the FULL Arrow type of the REAL selected
quotient CurrentSource. The complete groupoid laws are source
Arrow laws, not finite diagnostics. -/
noncomputable def originalRetainedOccupancyGroupoid
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    Groupoid (OriginalReachedOccupancy A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
  let C : ExactCalculus Q.source :=
    exactCalculus_of_homogeneous_CCO Q.source Q.homogeneous Q.cco
  let anchor : OriginalReachedOccupancy A B P base hBase E Kroot →
      Reached B.source Kroot :=
    originalReachedOccupancyAnchor A B P base hBase E Kroot
  let K := fun c : OriginalReachedOccupancy
      A B P base hBase E Kroot =>
    originalRetainedSelectedKernel A B P transport tp
      hOne Kroot E hE (anchor c)
  exact {
    Hom := fun a b => Arrow Q.source (K a) (K b)
    id := fun a => Arrow.id (K a)
    comp := fun R T => R.comp C T
    id_comp := fun R => Arrow.id_comp C R
    comp_id := fun R => Arrow.comp_id C R
    assoc := fun R T U => Arrow.comp_assoc C R T U
    inv := fun R => R.inv
    inv_comp := fun R => Arrow.inv_comp C R
    comp_inv := fun R => Arrow.comp_inv C R
  }

/-- The genuine selected occupancy groupoid is CONNECTED. For any
two actual occupancy objects, their chosen reached anchors have a
source connectingArrow, which maps to a whole selected Arrow by the
previously proved FULL C83 equivalence. No transport between
unrealized names or source SAP is invoked. -/
theorem originalRetainedOccupancyGroupoid_connected
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    ∀ a b : OriginalReachedOccupancy A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot,
      Nonempty (a ⟶ b) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  letI := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  intro a b
  let x := originalReachedOccupancyAnchor
    A B P base hBase E Kroot a
  let y := originalReachedOccupancyAnchor
    A B P base hBase E Kroot b
  let R := Reached.connectingArrow B.homogeneous C x y
  exact ⟨(originalRetainedSelectedArrowEquiv A B P transport tp
    hOne Kroot E hE x y) R⟩

end
end CCO.ExactEPGeometry
