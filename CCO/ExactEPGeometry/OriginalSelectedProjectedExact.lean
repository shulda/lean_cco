import CCO.ExactEPGeometry.OriginalSelectedFullExact
import CCO.ExactEPGeometry.OriginalCoherentProjectedArrowExact

/-!
# B062 C82–C83: genuine original-E projected gates and ALL Arrow images
in the actual one-representative-per-occupancy selected quotient.

The all-parent full-RAW exact gate and full Arrow image statements
are existing source-proved theorems, not hypotheses. The C82
selected retyping constructs real equivariant bijections of EVERY
local E-quotient class carrier to the actual chosen occupancy
representative and transports ALL intermediate RAW word witnesses.

These statements discharge the selected-source FULL EXACTNESS of
transported projected K and EVERY complete Arrow relation, with
no quotient SAP, hidden automorphism section, false diagonal
diversity atom or arbitrary mixed quotient descent. The subsequent
selected groupoid operations and corrected character are separate.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Every real all-parent projected exact gate K/e becomes a genuinely
FULL RAW-exact gate relation after transporting the selected E-class
representative, on the ACTUAL selected quotient source. -/
theorem original_selected_projected_gate_full_exact
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p : B.Sorts) (K : Kernel B.source p)
    (hNested : originalExactOnCurrentSort
      A B P transport base hOne E p ≤ current_kernel_exact_eq B K) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    letI : ∀ k : Q.Sorts, MulAction B.G (Q.Point k) := Q.action
    let D := originalSelectedSortRetyping
      A B P transport base hOne E
    FullExact
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).source
      (fun x y =>
        Quotient.image
          (fun a : B.Point p => (Quotient.mk'' a : Q.Point p))
          (fun b : B.Point p => (Quotient.mk'' b : Q.Point p))
          K.rel
          ((D.pointEquiv p).symm x) ((D.pointEquiv p).symm y)) := by
  exact original_selected_full_exact_of_allparent
    A B P transport base hOne E
    (Quotient.image
      (fun a : B.Point p =>
        (Quotient.mk'' a :
          (originalExactAllCurrentQuotientCurrentSource
            A B P transport base hOne E).Point p))
      (fun b : B.Point p =>
        (Quotient.mk'' b :
          (originalExactAllCurrentQuotientCurrentSource
            A B P transport base hOne E).Point p))
      K.rel)
    (original_coherent_allparent_projected_gate_exact
      A B P transport tp base hOne E p K hNested)

/-- C83 selected-source bridge STRENGTH FOR EVERY actual complete
current Arrow. Both original E-kernel nesting hypotheses are discharged
by the actual source wherever they occur (in particular, ALL reached
objects in the retained case). The result transports a GENUINE full
Arrow's entire projected binary relation into a FULL RAW-exact
relation on the selected named quotient source. -/
theorem original_selected_full_arrow_image_exact
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {i j : B.Sorts} (Kp : Kernel B.source i)
    (Kq : Kernel B.source j)
    (hEp : originalExactOnCurrentSort
      A B P transport base hOne E i ≤ current_kernel_exact_eq B Kp)
    (hEq : originalExactOnCurrentSort
      A B P transport base hOne E j ≤ current_kernel_exact_eq B Kq)
    (R : Arrow B.source Kp Kq) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    letI : ∀ k : Q.Sorts, MulAction B.G (Q.Point k) := Q.action
    let D := originalSelectedSortRetyping
      A B P transport base hOne E
    FullExact
      (originalExactSelectedQuotientCurrentSource
        A B P transport base hOne E).source
      (fun x y =>
        Quotient.image
          (fun a : B.Point i => (Quotient.mk'' a : Q.Point i))
          (fun b : B.Point j => (Quotient.mk'' b : Q.Point j))
          R.rel
          ((D.pointEquiv i).symm x) ((D.pointEquiv j).symm y)) := by
  exact original_selected_full_exact_of_allparent
    A B P transport base hOne E
    (Quotient.image
      (fun a : B.Point i =>
        (Quotient.mk'' a :
          (originalExactAllCurrentQuotientCurrentSource
            A B P transport base hOne E).Point i))
      (fun b : B.Point j =>
        (Quotient.mk'' b :
          (originalExactAllCurrentQuotientCurrentSource
            A B P transport base hOne E).Point j))
      R.rel)
    (original_coherent_allparent_arrow_image_exact
      A B P transport tp base hOne E Kp Kq hEp hEq R)

end
end CCO.ExactEPGeometry
