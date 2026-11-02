import CCO.ExactEPGeometry.OriginalRetainedSelectedGateClasses
import CCO.ExactEPGeometry.OriginalRetainedIdentityArrow

/-!
# B062 C84/C93: every old reached K-class has a canonical selected anchor image

For any genuine old reached parent b, its ORIGINAL E-occupancy class
has an actual reached anchor a. Since E is retained below the
canonical ORIGINAL gate G, the exact whole G-identity Arrow I_ba
is a real current Arrow, whose quotientMap is a bijection between
complete old K_b and K_a gate classes. The previously proved actual
C82/C83 full K_a ↔ K_a/E_a selected gate-class equivalence transports
these classes into the true selected E-occupancy source object.

This provides a bijection at EVERY source Reached object, even when
several old types merge to one E-occupancy object. The next naturality
lemma must compare all these maps with EVERY full source Arrow
normalized through its canonical old G-identity bridges.
No quotient SAP, automorphism-group section or hypothetical gate.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- The actual reached E-occupancy anchor is idempotent on its
own literal occupied component, not merely equivalent up to an
unspecified old type isomorphism. -/
theorem originalReachedOccupancyAnchor_idempotent
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (o : OriginalReachedOccupancy A B P base hOne E Kroot) :
    originalReachedOccupancyAnchorOf
        A B P base hOne E Kroot
        (originalReachedOccupancyAnchor
          A B P base hOne E Kroot o) =
      originalReachedOccupancyAnchor
        A B P base hOne E Kroot o := by
  let a := originalReachedOccupancyAnchor A B P base hOne E Kroot o
  have hClass :
      (Quotient.mk'' a :
        OriginalReachedOccupancy A B P base hOne E Kroot) = o :=
    originalReachedOccupancyAnchor_class A B P base hOne E Kroot o
  change originalReachedOccupancyAnchor A B P base hOne E Kroot
      (Quotient.mk'' a) =
    originalReachedOccupancyAnchor A B P base hOne E Kroot o
  exact congrArg (originalReachedOccupancyAnchor
    A B P base hOne E Kroot) hClass

/-- At EVERY actual old reached parent b, an honest old full G
identity bridge first transports K_b classes to the chosen
reached anchor of its E-occupancy component. The certified
projected full gate and actual selected class retyping then
transport them bijectively into the true selected quotient
point-action carrier. -/
noncomputable def originalReachedSelectedPointEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let a := originalReachedOccupancyAnchorOf
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E Kroot b
    (Reached.kernel B.homogeneous CB b).Class ≃
      (originalRetainedSelectedKernel
        A B P transport tp hOne Kroot E hE a).Class := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let a := originalReachedOccupancyAnchorOf
    A B P base hBase E Kroot b
  have hba : (originalExactOccupancySetoid A B P base hBase E).r
      b.val a.val :=
    originalReachedOccupancyAnchorOf_supported A B P
      base hBase E Kroot b
  let Iba := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b a hba
  exact (Iba.quotientEquiv B.homogeneous).trans
    (originalRetainedSelectedGateClassEquiv
      A B P transport tp hOne Kroot E hE a)

end
end CCO.ExactEPGeometry
