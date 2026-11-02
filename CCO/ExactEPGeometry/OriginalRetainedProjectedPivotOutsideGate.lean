import CCO.ExactEPGeometry.ProjectedSaturatedPivotOutsideGate
import CCO.ExactEPGeometry.OriginalCoherentAllparentGroupoid

/-!
# B062 C97: the REAL original E-quotient pivot avoids the true projected gate

At one actually reached current B parent, the genuine original exact
equivalence E is below the SAME certified original largest gate G, so
its real current trace e_b is below the reached gate K_b. The accepted
coherent all-parent typed quotient produces the genuine full-RAW-exact
projected gate K_b/e_b on the ACTUAL quotient source.

For any genuine old current relation R outside K_b, the image of its
two-sided e_b-saturation is disjoint from the WHOLE projected gate.
The argument uses the actual source-proved projected-gate pullback and
e_b ≤ K_b; quotient logical equality is not identified with K_b/e_b.

The source C97 instance for the selected odd pivot must still supply
the real maximal-gate witness that R is outside K_b, and the quotient
orbital theorem establishing that the image is ONE diversity atom.
No quotient SAP, fabricated group section, arbitrary mixed reverse
RAW descent or extra source hypothesis is introduced.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- On the ACTUAL all-parent E-quotient of B, the saturated image of
any real pivot outside the full reached K_b gate avoids its FULL
RAW-exact projected gate K_b/e_b. The original E≤G is the very
same source retention certificate used to construct K_b/e_b. -/
theorem originalRetainedAllparentProjectedPivotOutsideGate
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot)
    (R : B.Point b.val → B.Point b.val → Prop)
    (hOut : ∀ x y, R x y →
      ¬ (Reached.kernel B.homogeneous
          (exactCalculus_of_homogeneous_CCO
            B.source B.homogeneous B.cco) b).rel x y) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hBase E
    let e := (originalExactOnCurrentSort
      A B P transport base hBase E b.val).val.val
    let K := Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b
    let Kq := originalCoherentAllparentProjectedKernel
      A B P transport tp base hBase E b.val K
        (original_retained_current_E_below_full_gate
          A B P transport tp hOne Kroot E hE b)
    ∀ p q : Q.Point b.val,
      Quotient.image
        (fun x : B.Point b.val => (Quotient.mk'' x : Q.Point b.val))
        (fun x : B.Point b.val => (Quotient.mk'' x : Q.Point b.val))
        (fun x y => ∃ a c, e.r x a ∧ R a c ∧ e.r c y)
        p q → ¬ Kq.rel p q := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hBase E
  let e := (originalExactOnCurrentSort
    A B P transport base hBase E b.val).val.val
  let K := Reached.kernel B.homogeneous
    (exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco) b
  let hNested := original_retained_current_E_below_full_gate
    A B P transport tp hOne Kroot E hE b
  let Kq := originalCoherentAllparentProjectedKernel
    A B P transport tp base hBase E b.val K hNested
  let pi : B.Point b.val → Q.Point b.val := fun x => Quotient.mk'' x
  have hEK : e ≤ K.setoid := hNested
  change ∀ p q : Q.Point b.val,
    Quotient.image pi pi
      (fun x y => ∃ a c, e.r x a ∧ R a c ∧ e.r c y)
      p q → ¬ Kq.rel p q
  intro p q hImage hGate
  obtain ⟨x,y,hx,hy,hSat⟩ := hImage
  have hGateOld : Kq.rel (pi x) (pi y) := by
    simpa only [hx,hy] using hGate
  have hPull :=
    originalCoherentAllparentProjectedKernel_pullback
      A B P transport tp base hBase E b.val K hNested
  have hK : K.rel x y := by
    exact (Iff.of_eq (congrFun (congrFun hPull x) y)).mp hGateOld
  exact (saturatedPivot_disjointGate e K.setoid hEK R
    (fun x y hR => hOut x y hR) hSat) hK

end
end CCO.ExactEPGeometry
