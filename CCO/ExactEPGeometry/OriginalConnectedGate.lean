import CCO.ExactEPGeometry.OriginalCommonGateEquality
import CCO.APCharacter.SourcePhase

/-!
# B062 C56–C58: ONE ORIGINAL gate over every full connected reached component

The actual AP-only full-character source uses the FULL connected exact
rigid-groupoid `Reached S K`: its objects are all genuinely reached
current named sorts, its homs are ALL full exact Arrow relations, and
the accepted provider constructs a REAL connectingArrow between ANY
two reached objects.

The previous compiled C51–C56 proof applies to EVERY such genuine
connectingArrow (not a chosen generator). If the fixed ORIGINAL
source is ONE sort, the endpoint parent sort equality is derived from
the literal original sort uniqueness rather than assumed for the
specific pair of current objects. Consequently the canonical greatest
ORIGINAL full-exact lifts of all the actual current gates coincide,
up to the required old-sort equality transports.

This is a source-accurate C56 common-gate component. It does not yet
prove the full C57–C58 bidirectional groupoid correspondence or any
quotient tower / quotient SAP.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- For EVERY pair of objects in the genuine full connected source
groupoid, the canonical ORIGINAL greatest exact gates agree, not
only for selected generating edges. The source A01 one-original-sort
condition is supplied as literal uniqueness of the original sort.
It has no restriction on the number of current reached unary sorts. -/
theorem original_gates_constant_on_full_reached
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOriginalOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (b c : Reached B.source Kroot) :
    let C := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let Kb := Reached.kernel B.homogeneous C b
    let Kc := Reached.kernel B.homogeneous C c
    let Gb := PrefixExactLargestLift.largest A B P transport tp b.val
      (current_kernel_exact_eq B Kb)
    let Gc := PrefixExactLargestLift.largest A B P transport tp c.val
      (current_kernel_exact_eq B Kc)
    Gb = oldExactEqCast A.source
      (hOriginalOne (P.parent b.val) (P.parent c.val)) Gc := by
  dsimp only
  exact original_gates_equal_across_arrow
    A B P transport tp
    (hOriginalOne (P.parent b.val) (P.parent c.val))
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b)
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) c)
    (Reached.connectingArrow B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b c)

/-- Specialization to the ACTUAL source-phase selected full connected
groupoid: no arbitrary finite generating arrows, seed markings,
quotient actions or additional groupoid connectivity premises.
The genuine source phase has a real reached-object type, not a
hypothetical connected graph supplied by the consumer. -/
theorem original_gates_constant_in_actual_source_phase
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOriginalOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} {Kroot : Kernel B.source r}
    (_phase : APCharacter.SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b c : Reached B.source Kroot) :
    let C := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    let Kb := Reached.kernel B.homogeneous C b
    let Kc := Reached.kernel B.homogeneous C c
    let Gb := PrefixExactLargestLift.largest A B P transport tp b.val
      (current_kernel_exact_eq B Kb)
    let Gc := PrefixExactLargestLift.largest A B P transport tp c.val
      (current_kernel_exact_eq B Kc)
    Gb = oldExactEqCast A.source
      (hOriginalOne (P.parent b.val) (P.parent c.val)) Gc :=
  original_gates_constant_on_full_reached
    A B P transport tp hOriginalOne Kroot b c

end
end CCO.ExactEPGeometry
