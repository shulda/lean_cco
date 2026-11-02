import CCO.ExactEPGeometry.OriginalSelectedOccupancyActionMap
import CCO.ExactEPGeometry.OriginalAnchorGaugeZero

/-!
# B062 C93–C94: no hidden phase or K-class displacement at a real anchor

The source-to-selected K/E point map at a canonical reached
E-occupancy anchor is exactly the direct C82/C83 class equivalence.
The auxiliary identity transport I_aa is the WHOLE original gate
identity, and its quotient action fixes every K-class.
One must retain a dependent equality because the functor object
uses the chosen anchor of [a], while the direct class equivalence
uses a; their equality was PROVED by occupancy-anchor idempotence,
not postulated definitionally.

The result preserves the exact selected quotient point and its
projected gate class; there is no automorphism-group section,
quotient SAP or replacement by an arbitrary representative.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

theorem originalReachedSelectedActionPoint_anchor_heq
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (o : OriginalReachedOccupancy A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot)
    (q : (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco)
      (originalReachedOccupancyAnchor A B P (P.parent r)
        (fun k => hOne (P.parent r) k) E Kroot o)).Class) :
    let a := originalReachedOccupancyAnchor A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot o
    HEq
      (originalReachedSelectedActionPoint
        A B P transport tp hOne Kroot E hE a q)
      (originalRetainedSelectedGateClassEquiv
        A B P transport tp hOne Kroot E hE a q) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let a := originalReachedOccupancyAnchor A B P base hBase E Kroot o
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Ka := Reached.kernel B.homogeneous CB a
  have hFixed : originalReachedOccupancyAnchorOf
      A B P base hBase E Kroot a = a :=
    originalReachedOccupancyAnchor_idempotent
      A B P base hBase E Kroot o
  let J := originalExactOccupancySetoid A B P base hBase E
  let Iaa := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE
      a a (J.refl a.val)
  have hId : Iaa = Arrow.id Ka :=
    original_retained_identity_arrow_self
      A B P transport tp hOne Kroot E hE a
  have hAct : Iaa.quotientMap B.homogeneous q = q := by
    rw [hId]
    exact Arrow.quotientMap_id B.homogeneous q
  cases hFixed
  change HEq
    (((Iaa.quotientEquiv B.homogeneous).trans
      (originalRetainedSelectedGateClassEquiv
        A B P transport tp hOne Kroot E hE a)) q)
    ((originalRetainedSelectedGateClassEquiv
      A B P transport tp hOne Kroot E hE a) q)
  exact HEq.of_eq (by
    change (originalRetainedSelectedGateClassEquiv
      A B P transport tp hOne Kroot E hE a)
        (Iaa.quotientMap B.homogeneous q) =
      (originalRetainedSelectedGateClassEquiv
        A B P transport tp hOne Kroot E hE a) q
    rw [hAct])

end
end CCO.ExactEPGeometry
