import CCO.ExactEPGeometry.OriginalDiscardedOccupancy
import CCO.ExactEPGeometry.OriginalConnectedGate

/-!
# B062 C77: real retained-E occupancy inside the selected original gate

In contrast to the discarded case C73-C76, here the ORIGINAL full
RAW-exact E lies below the genuine greatest original gate of the actual
SourcePhase. Every individual old E-class meeting a current unary
parent i meets EVERY parent j in its real E-occupancy component.
The SAME witnesses also belong to the selected ORIGINAL exact gate.

The following two source consequences are the classwise/nonempty
input to C77's genuinely typed full-bridge construction. They do NOT
by themselves assert a current full Arrow, reachability of j, a
quotient action, or a retained occupancy graph.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C77's classwise old-G occupancy witness. For EVERY actual point
of type i and EVERY E-supported type j, find a real point of type j
related by the original EXACT selected gate. No E-class is replaced
by an arbitrary pair of representatives. -/
theorem original_retained_each_class_hits_original_gate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (i j : B.Sorts)
    (hSupported : (originalExactOccupancySetoid
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E).r i j)
    (x : B.Point i) :
    ∃ y : B.Point j,
      (PrefixExactLargestLift.largest A B P transport tp r
        (current_kernel_exact_eq B Kroot))
        ((hOne (P.parent r) (P.parent i)).symm ▸ P.point i x)
        ((hOne (P.parent r) (P.parent j)).symm ▸ P.point j y) := by
  have hSupport : prefixSupport P
      (originalExactGlobalRelation A (P.parent r)
        (fun k => hOne (P.parent r) k) E) i j := hSupported
  obtain ⟨y,hxy⟩ :=
    (originalExactClass_occupies_supported_type
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E i j x).mp hSupport
  exact ⟨y,hE hxy⟩

/-- The whole ORIGINAL selected gate genuinely has a nonempty
i,j trace on every E-supported current sort pair. In particular
this never invents a bridge on an unoccupied pair of current types. -/
theorem original_retained_original_gate_trace_nonempty
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (i j : B.Sorts)
    (hSupported : (originalExactOccupancySetoid
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E).r i j) :
    ∃ x : B.Point i, ∃ y : B.Point j,
      (PrefixExactLargestLift.largest A B P transport tp r
        (current_kernel_exact_eq B Kroot))
        ((hOne (P.parent r) (P.parent i)).symm ▸ P.point i x)
        ((hOne (P.parent r) (P.parent j)).symm ▸ P.point j y) := by
  let x : B.Point i := Classical.choice (B.source.nonemptySort i)
  obtain ⟨y,hxy⟩ :=
    original_retained_each_class_hits_original_gate
      A B P transport tp hOne Kroot E hE i j hSupported x
  exact ⟨x,y,hxy⟩

end
end CCO.ExactEPGeometry
