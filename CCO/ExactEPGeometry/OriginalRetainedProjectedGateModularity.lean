import CCO.ExactEPGeometry.ProjectedNestedGateModularity
import CCO.ExactEPGeometry.OriginalCoherentAllparentGroupoid

/-!
# B062 C100: modularity for the REAL full K_b/E_b gate of a retained step

At every genuinely reached current parent b of a retained original
maximal-character step, the actual trace e_b of the SAME original
full exact E is below the true reached full gate K_b. The coherent
typed quotient provider already constructs K_b/e_b as a genuine
FULL RAW-exact gate in the ACTUAL all-parent E-quotient source.

For every old current relation R, the intersection of that projected
gate with the projected e_b-two-sided saturation of R is EXACTLY the
projection of the e_b-saturation of K_b∩R. This is the source
instantiation of the C100 relational modular identity, with every
original and quotient equality retained.

The further identification e_b;X;e_b = e_b∨X needs the actual
commuting equivalences from the genuine selected odd pivot; it is
not smuggled into this statement. Projected maximality and the
full quotient safe tower remain separate source obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

theorem originalRetainedAllparentProjectedGateModularity
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
    (R : B.Point b.val → B.Point b.val → Prop) :
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
    let pi : B.Point b.val → Q.Point b.val :=
      fun x => Quotient.mk'' x
    ∀ p q : Q.Point b.val,
      (Kq.rel p q ∧
        Quotient.image pi pi
          (fun x y => ∃ a c, e.r x a ∧ R a c ∧ e.r c y) p q) ↔
      Quotient.image pi pi
        (fun x y => ∃ a c, e.r x a ∧
          (K.rel a c ∧ R a c) ∧ e.r c y) p q := by
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
  let pi : B.Point b.val → Q.Point b.val :=
    fun x => Quotient.mk'' x
  have hEK : e ≤ K.setoid := hNested
  have hpi : ∀ x y, pi x = pi y → K.rel x y := by
    intro x y h
    exact hEK (Quotient.exact h)
  change ∀ p q : Q.Point b.val,
    ((K.projectedSetoid pi Quotient.mk''_surjective hpi).r p q ∧
      Quotient.image pi pi
        (fun x y => ∃ a c, e.r x a ∧ R a c ∧ e.r c y) p q) ↔
    Quotient.image pi pi
      (fun x y => ∃ a c, e.r x a ∧
        (K.rel a c ∧ R a c) ∧ e.r c y) p q
  intro p q
  exact projectedNestedGate_inter_saturation_iff K e hEK
    pi Quotient.mk''_surjective hpi R p q

end
end CCO.ExactEPGeometry
