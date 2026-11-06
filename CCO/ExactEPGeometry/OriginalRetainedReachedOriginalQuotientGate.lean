import CCO.ExactEPGeometry.OriginalOneSortLargestQuotientTrace
import CCO.ExactEPGeometry.OriginalRetainedProjectedGateBase

/-!
# B062 C102: full ORIGINAL E-quotient largest gate on EVERY reached parent

The canonical ORIGINAL gate of a retained SourcePhase is transported
coherently across ALL reached current parents, by the already proved
source C56 old-gate identity and largest-lift adjunction. The single
original E is transported by actual equality of original sort names.

For each genuinely reached current parent b, the actual C82 theorem
already proves E|b <= its complete current full gate K_b. Applying
the true E2/E3 right adjunction gives the ORIGINAL transported E_b <=
the genuine largest ORIGINAL G_b=L_b(K_b). Hence the C102 exact
one-original-sort quotient-gate theorem applies at this SAME b.

The resulting G_b/E_b is full RAW exact in the literal original one-sort
canonical E-quotient, has precisely K_b as current trace, and dominates
EVERY other full-exact original quotient equivalence with trace <=K_b.
There is no new gate/nesting assumption, quotient SAP, invented group
section, or appeal to a future quotient step.

This is still the original ONE-sort quotient source; the already-built
selected one-parent-per-E-occupancy quotient prefix and entire marked
age/whole safe tower are separate remaining C102/C103–C105 contracts.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Source C102 at ALL truly reached parents of one retained maximal
character SourcePhase: the same original E below the ORIGINAL root G
gives an actual full-exact largest G_b/E_b, exact current K_b trace,
and the complete universal exact-fibre property on the actual original
one-sort quotient. -/
theorem originalRetainedReachedOriginalQuotientGate_complete
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
    let Kb := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    let same : P.parent r = P.parent b.val :=
      hOne (P.parent r) (P.parent b.val)
    let Eb : ExactEq A.source (P.parent b.val) :=
      oldExactEqCast A.source same.symm E
    let base := P.parent b.val
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let J := originalExactSourceKernelFamily A base hBase Eb
    let W := originalExactSourceKernelWords A base hBase Eb
    let hW := originalExactSourceKernelWords_relation A base hBase Eb
    let Q0 := CCO.ExactCRT.CanonicalTyped.source
      A.source A.homogeneous J W hW
    let pi : A.Point base → Quotient (J base) :=
      CCO.ExactCRT.CanonicalTyped.projection J base
    let Gb := PrefixExactLargestLift.largest A B P transport tp b.val
      (current_kernel_exact_eq B Kb)
    FullExact Q0 (CCO.ExactCRT.quotientRelation pi pi
      (fun a z : A.Point base => Gb a z)) ∧
    (∀ x y : B.Point b.val,
      CCO.ExactCRT.quotientRelation pi pi
        (fun a z : A.Point base => Gb a z)
        (pi (P.point b.val x)) (pi (P.point b.val y)) ↔
          Kb.rel x y) ∧
    ∀ Z : Kernel Q0 base,
      (∀ x y : B.Point b.val,
        Z.rel (pi (P.point b.val x)) (pi (P.point b.val y)) →
          Kb.rel x y) →
      ∀ q s : Quotient (J base), Z.rel q s →
        CCO.ExactCRT.quotientRelation pi pi
          (fun a z : A.Point base => Gb a z) q s := by
  let Kb := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco) b
  let same : P.parent r = P.parent b.val :=
    hOne (P.parent r) (P.parent b.val)
  let Eb : ExactEq A.source (P.parent b.val) :=
    oldExactEqCast A.source same.symm E
  let Gb := PrefixExactLargestLift.largest A B P transport tp b.val
    (current_kernel_exact_eq B Kb)
  have hNested :=
    original_retained_current_E_below_full_gate
      A B P transport tp hOne Kroot E hE b
  have hTrace :
      PrefixExactRestriction.rho A B P transport b.val Eb ≤
        current_kernel_exact_eq B Kb := by
    change PrefixExactRestriction.rho A B P transport b.val
      (oldExactEqCast A.source same.symm E) ≤
        current_kernel_exact_eq B Kb at hNested
    exact hNested
  have hEb : Eb ≤ Gb :=
    ((PrefixExactLargestLift.largest_spec
      A B P transport tp b.val
        (current_kernel_exact_eq B Kb)).2 Eb).mp hTrace
  exact originalOneSortLargestQuotientGate_complete
    A B P transport tp hOne b.val Kb Eb hEb

end
end CCO.ExactEPGeometry
