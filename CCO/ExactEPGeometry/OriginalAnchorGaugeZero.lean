import CCO.ExactEPGeometry.OriginalReachedGlobalGauge

/-!
# B062 C84/C94: the genuine global original phase offset vanishes at anchors

Every ORIGINAL E-occupancy class of truly reached current types
has one actual reached anchor, selected from its own quotient class.
The C84 global offset is the phase of the full original G-identity
bridge from a reached object to its canonical anchor. At the anchor
itself this bridge is the WHOLE exact gate identity, so the offset
is exactly zero. No original logical identity or noncanonical
point section replaces that gate.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

theorem originalReachedGlobalOffset_anchor_zero
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (o : OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot) :
    originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE
      (originalReachedOccupancyAnchor A B P (P.parent r)
        (fun i => hOne (P.parent r) i) E Kroot o) = 0 := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let a := originalReachedOccupancyAnchor A B P base hBase E Kroot o
  have hClass : (Quotient.mk'' a :
      OriginalReachedOccupancy A B P base hBase E Kroot) = o :=
    originalReachedOccupancyAnchor_class A B P base hBase E Kroot o
  have hAnchor :
      originalReachedOccupancyAnchorOf A B P base hBase E Kroot a = a := by
    change originalReachedOccupancyAnchor A B P base hBase E Kroot
      (Quotient.mk'' a) = a
    exact congrArg
      (originalReachedOccupancyAnchor A B P base hBase E Kroot) hClass
  change originalRetainedAnchorOffset A B P transport tp
    hOne Kroot phase E hE
    (originalReachedOccupancyAnchorOf A B P base hBase E Kroot a) a = 0
  rw [hAnchor]
  exact originalRetainedAnchorOffset_anchor_zero
    A B P transport tp hOne Kroot phase E hE a

end
end CCO.ExactEPGeometry
