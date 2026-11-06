import CCO.ExactEPGeometry.ActualDiscardedBit
import CCO.ExactEPGeometry.OriginalConnectedGate

/-!
# B062 C73–C75: ORIGINAL E not below G forces each active class to flip

Fix an ACTUAL homogeneous AP+HOM CCO current source B and a genuine
full character SourcePhase for a root exact gate Kroot. Its entire
reachable component is the full exact rigid groupoid, not a list
of chosen generating arrows. The PREVIOUSLY PROVED common ORIGINAL
maximal exact gate theorem identifies the greatest original lifts
at EVERY active reached parent when the fixed original source A has
ONE sort (with its actual original sort equalities).

If original FULL RAW-exact E is NOT below that root original gate,
its REAL exact restriction at EVERY reached parent cannot lie below
the corresponding current gate. This follows from the true E1/E2/E3
right adjoint and full-groupoid gate equality; it does not assume
an independent current nonrefinement property.

Apply the proved CURRENT C74–C75 class-by-class odd-arrow argument.
Every real x in every reached active current parent has a REAL
original-E-equivalent point y in the SAME parent with the opposite
actual legal new bit. Thus EACH E-class represented there meets both
children. No group section, quotient SAP, false transported marking
or abstract unproved common old gate is inserted.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C73, actual all-active-parent strength: noncontainment of one
ORIGINAL full RAW-exact E in the genuine root greatest old gate
implies its ACTUAL exact restriction is not under the current gate
of EVERY reached active parent. The original sort equality is
provided by the frozen one-original-sort hypothesis, not an
unjustified identification of distinct current unary sort names. -/
theorem original_not_below_root_gate_all_active
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    let C := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let Kb := Reached.kernel B.homogeneous C b
    let hSame := hOne (P.parent r) (P.parent b.val)
    ¬ PrefixExactRestriction.rho A B P transport b.val
        (oldExactEqCast A.source hSame.symm E) ≤
      current_kernel_exact_eq B Kb := by
  dsimp only
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  let hSame := hOne (P.parent r) (P.parent b.val)
  let Eb : ExactEq A.source (P.parent b.val) :=
    oldExactEqCast A.source hSame.symm E
  let Fb : ExactEq B.source b.val := current_kernel_exact_eq B Kb
  let Gb : ExactEq A.source (P.parent b.val) :=
    PrefixExactLargestLift.largest A B P transport tp b.val Fb
  let Gr : ExactEq A.source (P.parent r) :=
    PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)
  have hRoot : Reached.kernel B.homogeneous C (Reached.root Kroot) =
      Kroot :=
    Reached.root_kernel B.homogeneous C (A := Kroot)
  have hGate : Gr = oldExactEqCast A.source hSame Gb := by
    have h := original_gates_constant_on_full_reached
      A B P transport tp hOne Kroot (Reached.root Kroot) b
    dsimp only at h
    rw [hRoot] at h
    exact h
  have hNotB : ¬ Eb ≤ Gb := by
    intro hEb
    have hCast : E ≤ oldExactEqCast A.source hSame Gb := by
      have h :=
        oldExactEqCast_mono A.source hSame Eb Gb hEb
      change oldExactEqCast A.source hSame
          (oldExactEqCast A.source hSame.symm E) ≤
        oldExactEqCast A.source hSame Gb at h
      simpa only [oldExactEqCast_cancel] using h
    have hOld : E ≤ Gr := by
      rw [hGate]
      exact hCast
    exact hNot hOld
  intro hCurrent
  apply hNotB
  exact ((PrefixExactLargestLift.largest_spec
    A B P transport tp b.val Fb).2 Eb).mp hCurrent

/-- C74–C75 for ACTUAL original E: EACH E-class meeting EVERY active
parent has a real representative in its opposite legal new child.
The old source single-sort hypothesis, the genuine SOURCE-selected
common gate, the E1/E2/E3 adjunction and actual full odd Arrow
are all discharged in this proof. -/
theorem original_discarded_each_active_class_opposite_child
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
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot)
    (x : B.Point b.val) :
    let hSame := hOne (P.parent r) (P.parent b.val)
    ∃ y : B.Point b.val,
      (PrefixExactRestriction.rho A B P transport b.val
        (oldExactEqCast A.source hSame.symm E)) x y ∧
      UnarySource.mark (SingleStep.identification B phase) ⟨b.val,y⟩ =
        UnarySource.mark (SingleStep.identification B phase) ⟨b.val,x⟩ +
          (1 : Bit) := by
  dsimp only
  let hSame := hOne (P.parent r) (P.parent b.val)
  let Eb := PrefixExactRestriction.rho A B P transport b.val
    (oldExactEqCast A.source hSame.symm E)
  have hNotB :=
    original_not_below_root_gate_all_active
      A B P transport tp hOne Kroot E hNot b
  exact current_not_below_gate_each_class_opposite_bit
    B Kroot phase b Eb hNotB x

end
end CCO.ExactEPGeometry
