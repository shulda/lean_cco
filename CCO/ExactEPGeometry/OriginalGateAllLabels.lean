import CCO.ExactEPGeometry.OriginalGateLabelStep
import CCO.ExactEPGeometry.OriginalGateTargetTrace

/-!
# B062 C61: one canonical ORIGINAL gate preserves ALL next unary labels

The real root full exact gate is first lifted to an ORIGINAL exact
equivalence via E1–E3. For any actual reached current sort, the
full Reached.rootArrow, NOT a chosen generating subset, proves that
this same original exact gate restricts precisely to the sort's
actual current gate (C55/C56). The genuine full-character marked
age then forces the same child bit for every pair under that gate.

An inactive current sort has its unique actual phase bit, independently
of E. Both arguments use the SAME genuine SourcePhase and successor
identification, and only the true ONE-original-sort equality transport.

No quotient SAP, group-action section, stronger exactness premise,
imaginary representatives or arbitrary external marking.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry

noncomputable section

/-- If an ORIGINAL exact equivalence E lies below the largest ORIGINAL
exact lift of the active root gate, then E preserves the LITERAL new
child tag of EVERY active object b in the FULL reached groupoid.
The sole extra condition is actual ONE-original-sort equality. -/
theorem original_below_largest_preserves_reached_child
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {p : B.Sorts} (K : Kernel B.source p)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (E : ExactEq A.source (P.parent p))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B K))
    (b : Reached B.source K) (x y : B.Point b.val)
    (hxy : E
      ((hOne (P.parent p) (P.parent b.val)).symm ▸ P.point b.val x)
      ((hOne (P.parent p) (P.parent b.val)).symm ▸ P.point b.val y)) :
    UnarySource.tag (SingleStep.identification B phase) b.val x =
      UnarySource.tag (SingleStep.identification B phase) b.val y := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  let hSame := hOne (P.parent p) (P.parent b.val)
  let G := PrefixExactLargestLift.largest A B P transport tp p
    (current_kernel_exact_eq B K)
  have hOld : G
      (hSame.symm ▸ P.point b.val x)
      (hSame.symm ▸ P.point b.val y) := hE hxy
  have hGate :
      Kb.rel x y ↔
        G (hSame.symm ▸ P.point b.val x)
          (hSame.symm ▸ P.point b.val y) :=
    current_arrow_original_gate_target_trace
      A B P transport tp hSame K Kb
      (Reached.rootArrow B.homogeneous C b) x y
  exact canonical_phase_gate_preserves_child_tag
    B phase b x y (hGate.mpr hOld)

/-- The same original exact E, if below the ACTUAL source-selected
old root gate, preserves the new child bit on EVERY current parent,
active or inactive. Inactive bits are uniquely valid by the actual
phase mask, and active bits are handled by a real full reached arrow. -/
theorem original_below_largest_preserves_all_next_child
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {p : B.Sorts} (K : Kernel B.source p)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (E : ExactEq A.source (P.parent p))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B K))
    (i : B.Sorts) (x y : B.Point i)
    (hxy : E
      ((hOne (P.parent p) (P.parent i)).symm ▸ P.point i x)
      ((hOne (P.parent p) (P.parent i)).symm ▸ P.point i y)) :
    UnarySource.tag (SingleStep.identification B phase) i x =
      UnarySource.tag (SingleStep.identification B phase) i y := by
  classical
  by_cases hActive : Nonempty (Bridge B.source K i)
  · let b : Reached B.source K := ⟨i,hActive⟩
    exact original_below_largest_preserves_reached_child A B P
      transport tp hOne K phase E hE b x y hxy
  · exact canonical_inactive_parent_child_tag_unique B phase
      i hActive x y

end
end CCO.ExactEPGeometry
