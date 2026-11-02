import CCO.ExactEPGeometry.OriginalRetainedProjectedPivotOutsideGate
import CCO.APCharacter.SourcePhase

/-!
# B062 C97: REAL source odd full Arrow stays diversity after E projection

For a retained genuine maximal-character SourcePhase, every reached
parent b has a TRUE full exact nonidentity odd Arrow
`phase.atSort b`. Its entire relation is disjoint from the whole
current gate K_b: two complete arrows containing the same real pair
are equal, so a common pair with the full gate identity would
contradict the certified nonidentity theorem.

The actual old E trace is below K_b because the retained original
E≤G. Thus the E-saturated odd relation, projected onto the REAL
all-parent E-quotient source, is disjoint from the PROVED full RAW
exact quotient gate K_b/E_b. In particular this projected odd arrow
cannot become logical quotient equality.

The C97 source pivot is still a single selected quotient orbital:
showing its atomness via I10 and carrying this disjointness through
the actual occupancy selected-sort retyping are separate obligations.
No quotient SAP, assumed group section or fake diagonal is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

theorem originalRetainedAllparentOddOutsideProjectedGate
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
    (b : Reached B.source Kroot) :
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
    let odd := phase.atSort b
    ∀ p q : Q.Point b.val,
      Quotient.image
        (fun x : B.Point b.val => (Quotient.mk'' x : Q.Point b.val))
        (fun x : B.Point b.val => (Quotient.mk'' x : Q.Point b.val))
        (fun x y => ∃ a c, e.r x a ∧ odd.rel a c ∧ e.r c y)
        p q → ¬ Kq.rel p q := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  let odd := phase.atSort b
  have hOut : ∀ x y : B.Point b.val, odd.rel x y → ¬K.rel x y := by
    intro x y hOdd hK
    have hEq : odd = Arrow.id K :=
      odd.eq_of_common_real_pair B.homogeneous (Arrow.id K) hOdd hK
    exact (phase.atSort_nonidentity b) hEq
  exact originalRetainedAllparentProjectedPivotOutsideGate
    A B P transport tp hOne Kroot E hE b odd.rel hOut

end
end CCO.ExactEPGeometry
