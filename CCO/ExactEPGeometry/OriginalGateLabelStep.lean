import CCO.ExactEPGeometry.ActualGateBitPreservation
import CCO.ExactEPGeometry.PrefixExactLargestLift

/-!
# B062 C61: actual ORIGINAL exact gate candidates preserve phase labels

The genuine source-gate bit theorem is now consumed at an ACTUAL
old-to-current prefix, whose two-way RAW-exact transport and fixed
middle-sort (TP) were previously proved. Any ORIGINAL full-RAW-exact
equivalence E lying beneath the greatest original lift L_p(K_p) has
literal restriction inside the chosen true current gate K_p; its
real pair witnesses therefore have equal child labels at that root.

On INACTIVE current unary sorts there is exactly one valid child
bit, by the actual SourcePhase mask, and it is read from the same
constructed marked-age identification. Thus all pairs of points of
one inactive sort have equal next child label, independently of E.

The remaining all-active-objects step uses the full connected original
gate equality (C56) to transport the result from root to all reached
objects; no group section, quotient SAP or arbitrary source assumption.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry

noncomputable section

/-- A real original FULL-RAW-exact E below the canonical largest
old exact lift of the ACTUAL current root gate preserves the
literal next child name of the root. This is an old-to-current
SOURCE theorem, not an assumed action of the quotient automorphisms. -/
theorem original_below_largest_preserves_root_child
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    {p : B.Sorts} (K : Kernel B.source p)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (E : ExactEq A.source (P.parent p))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp p
      (current_kernel_exact_eq B K))
    (x y : B.Point p)
    (hxy : E (P.point p x) (P.point p y)) :
    UnarySource.tag (SingleStep.identification B phase) p x =
      UnarySource.tag (SingleStep.identification B phase) p y := by
  let G := PrefixExactLargestLift.largest A B P transport tp p
    (current_kernel_exact_eq B K)
  have hOld : G (P.point p x) (P.point p y) := hE hxy
  have hCurrent :
      (PrefixExactRestriction.rho A B P transport p G) x y :=
    (PrefixExactRestriction.rho_iff A B P transport p G x y).mpr hOld
  have hG : PrefixExactRestriction.rho A B P transport p G =
      current_kernel_exact_eq B K :=
    (PrefixExactLargestLift.largest_spec A B P transport tp p
      (current_kernel_exact_eq B K)).1
  rw [hG] at hCurrent
  have hRoot :
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco)
        (Reached.root K)).rel x y := by
    rw [Reached.root_kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := K)]
    exact hCurrent
  exact canonical_phase_gate_preserves_child_tag B phase
    (Reached.root K) x y hRoot

/-- C61 for ANY genuine INACTIVE current parent sort. The actual
phase allows a unique bit on that sort, and both points carry
their true bits from its constructed marked-age identification.
No gate action or additional SAP premise is needed. -/
theorem canonical_inactive_parent_child_tag_unique
    (B : CurrentSource.{u,v,w,t})
    {i : B.Sorts} {K : Kernel B.source i}
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (p : B.Sorts)
    (hInactive : ¬Nonempty (Bridge B.source K p))
    (x y : B.Point p) :
    UnarySource.tag (SingleStep.identification B phase) p x =
      UnarySource.tag (SingleStep.identification B phase) p y := by
  let I := SingleStep.identification B phase
  have hvx : phase.validBit p (UnarySource.mark I ⟨p,x⟩) :=
    (UnarySource.global_marking I).1 ⟨p,x⟩
  have hvy : phase.validBit p (UnarySource.mark I ⟨p,y⟩) :=
    (UnarySource.global_marking I).1 ⟨p,y⟩
  apply Subtype.ext
  exact phase.inactive_bit_unique hInactive hvx hvy

end
end CCO.ExactEPGeometry
