import CCO.ExactEPGeometry.OriginalRetainedBridge
import CCO.ExactEPGeometry.OriginalArrowReverseBridge

/-!
# B062 C78: a genuine whole G-identity bridge on retained occupancy

For one actual retained SourcePhase and every two of its FULL reached
parents in the SAME original E-occupancy component, the true
original maximal exact G has a REAL pair witness on these parents.
Its entire trace is a genuine CURRENT full RAW-exact Arrow
between their ACTUAL gates, constructed through the proved C57
original-to-current bridge converse and fixed-middle (TP).

This is not an arbitrary relation or a chosen groupoid generating
edge. The original Arrow is the true whole identity Arrow.id G.
Only its current TYPE trace may have different endpoints.
-/ 

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C78 actual whole exact gate-identity current arrow, along any
pair of active reached parent types with genuine original E-support.
The target gate restriction is obtained from a REAL full source
connectingArrow (C56), not an additional assumed exactness theorem. -/
noncomputable def original_retained_identity_arrow
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot)
    (hSupported : (originalExactOccupancySetoid
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E).r b.val c.val) :
    Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) c) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  let Kc := Reached.kernel B.homogeneous C c
  let Gr := PrefixExactLargestLift.largest A B P transport tp r
    (current_kernel_exact_eq B Kroot)
  let Gb := PrefixExactLargestLift.largest A B P transport tp b.val
    (current_kernel_exact_eq B Kb)
  let hbi := hOne (P.parent r) (P.parent b.val)
  let hbc := hOne (P.parent r) (P.parent c.val)
  let hij := hOne (P.parent b.val) (P.parent c.val)
  let G : Kernel A.source (P.parent b.val) :=
    original_largest_gate_kernel A B P transport tp b.val Kb
  have hRootGate : Gr = oldExactEqCast A.source hbi Gb := by
    have h := original_gates_constant_on_full_reached
      A B P transport tp hOne Kroot (Reached.root Kroot) b
    dsimp only at h
    rw [Reached.root_kernel B.homogeneous C (A := Kroot)] at h
    exact h
  have hLocalGate : oldExactEqCast A.source hbi.symm Gr = Gb := by
    have h := congrArg (oldExactEqCast A.source hbi.symm) hRootGate
    simpa only [oldExactEqCast_cancel] using h
  have hSpec : PrefixExactRestriction.rho A B P transport b.val Gb =
      current_kernel_exact_eq B Kb :=
    (PrefixExactLargestLift.largest_spec
      A B P transport tp b.val (current_kernel_exact_eq B Kb)).1
  have hGateP (x z : B.Point b.val) :
      G.rel (P.point b.val x) (P.point b.val z) ↔ Kb.rel x z := by
    change Gb (P.point b.val x) (P.point b.val z) ↔ Kb.rel x z
    calc
      Gb (P.point b.val x) (P.point b.val z) ↔
          (PrefixExactRestriction.rho A B P transport b.val Gb) x z :=
        (PrefixExactRestriction.rho_iff A B P transport b.val Gb x z).symm
      _ ↔ Kb.rel x z := by
        rw [hSpec]
        exact Iff.rfl
  let conn : Arrow B.source Kb Kc :=
    Reached.connectingArrow B.homogeneous C b c
  have hGateQ (y z : B.Point c.val) :
      G.rel (hij.symm ▸ P.point c.val y)
          (hij.symm ▸ P.point c.val z) ↔ Kc.rel y z :=
    (current_arrow_original_gate_target_trace
      A B P transport tp hij Kb Kc conn y z).symm
  let hWitness := original_retained_original_gate_trace_nonempty
    A B P transport tp hOne Kroot E hE b.val c.val hSupported
  let x : B.Point b.val := Classical.choose hWitness
  let y : B.Point c.val :=
    Classical.choose (Classical.choose_spec hWitness)
  have hGroot : Gr
      (hbi.symm ▸ P.point b.val x)
      (hbc.symm ▸ P.point c.val y) :=
    Classical.choose_spec (Classical.choose_spec hWitness)
  have hReal : ∃ x : B.Point b.val, ∃ y : B.Point c.val,
      (Arrow.id G).rel (P.point b.val x)
        (hij.symm ▸ P.point c.val y) := by
    refine ⟨x,y,?_⟩
    change Gb (P.point b.val x) (hij.symm ▸ P.point c.val y)
    rw [← hLocalGate]
    apply (oldExactEqCast_iff A.source hbi.symm Gr
      (P.point b.val x) (hij.symm ▸ P.point c.val y)).mpr
    rw [original_parent_cast_comp hbi hbc hij (P.point c.val y)]
    exact hGroot
  exact original_arrow_trace_to_current_arrow
    A B P transport tp hij G Kb Kc
    hGateP hGateQ (Arrow.id G) hReal

/-- The C78 arrow has literally the FULL real original G trace on
its two displayed current endpoint sorts. This records the actual
old-to-current correspondence needed for C79's identity-bridge
composition equation, not merely the existence of some arrow. -/
theorem original_retained_identity_arrow_iff
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot)
    (hSupported : (originalExactOccupancySetoid
      A B P (P.parent r) (fun k => hOne (P.parent r) k) E).r b.val c.val)
    (x : B.Point b.val) (y : B.Point c.val) :
    (original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b c hSupported).rel x y ↔
    (original_largest_gate_kernel A B P transport tp b.val
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b)).rel
      (P.point b.val x)
      ((hOne (P.parent b.val) (P.parent c.val)).symm ▸
        P.point c.val y) := Iff.rfl

end
end CCO.ExactEPGeometry
