import CCO.ExactEPGeometry.OriginalCoherentProjectedArrowExact
import CCO.RigidGroupoid.Geometry.Endpoint

/-!
# B062 C83: actual all-parent quotient gates and complete Hom equivalence

The full current original-E coherent typed quotient is already an ACTUAL
CurrentSource. C82 proved its projected gate exact at every endpoint,
without assuming selected-subsort reverse exact descent or quotient SAP.

We use exactly the accepted C16/C17 endpoint theorem on that actual
source to construct the whole original-to-quotient Arrow equivalence
for ANY pair of current exact gates containing local original E.
The quotient points, action, orbital colours, kernel words and
endpoint full-RAW exactness are all the real simultaneous quotient
providers; no automorphism-group section or invented quotient orbit.

The resulting Hom equivalence is for the ALL-parent quotient, not yet
the selected one-parent-per-occupancy quotient. Selecting sorts later
is a separate nontrivial source obligation.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C83: the projected gate is a GENUINE full exact Kernel of the
actual all-parent quotient CurrentSource. The direct quotient gate
exactness comes from the proved coherent-current RAW word TI, not a
postulated hProjected provider. -/
noncomputable def originalCoherentAllparentProjectedKernel
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p : B.Sorts) (K : Kernel B.source p)
    (hNested : originalExactOnCurrentSort A B P transport
      base hOne E p ≤ current_kernel_exact_eq B K) :
    Kernel (originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E).source p := by
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  let π : B.Point p → Q.Point p := fun x => Quotient.mk'' x
  have hNestedπ : ∀ x y, π x = π y → K.rel x y := by
    intro x y hxy
    exact hNested (Quotient.exact hxy)
  have hExact : FullExact Q.source
      (K.projectedSetoid π (Quotient.mk''_surjective) hNestedπ).r := by
    change FullExact Q.source (Quotient.image π π K.rel)
    exact original_coherent_allparent_projected_gate_exact
      A B P transport tp base hOne E p K hNested
  exact K.projectedKernel Q.source π
    (Quotient.mk''_surjective) hNestedπ hExact

/-- The whole projected gate relation pulls back to the real
original current full gate, not to logical identity or just e_p. -/
theorem originalCoherentAllparentProjectedKernel_pullback
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    (p : B.Sorts) (K : Kernel B.source p)
    (hNested : originalExactOnCurrentSort A B P transport
      base hOne E p ≤ current_kernel_exact_eq B K) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    let π : B.Point p → Q.Point p := fun x => Quotient.mk'' x
    GroupActions.pullback π π
      (originalCoherentAllparentProjectedKernel
        A B P transport tp base hOne E p K hNested).rel = K.rel := by
  dsimp only
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  let π : B.Point p → Q.Point p := fun x => Quotient.mk'' x
  have hNestedπ : ∀ x y, π x = π y → K.rel x y := by
    intro x y hxy
    exact hNested (Quotient.exact hxy)
  exact K.projected_pullback π (Quotient.mk''_surjective) hNestedπ

/-- Full C83 ALL-PARENT exact bridge correspondence: EVERY actual
complete current Arrow has an exactly reversible representation as
a whole full-RAW exact Arrow on the literal all-parent quotient,
with the real projected gates. The selected-sort step is still open. -/
noncomputable def originalCoherentAllparentArrowEquiv
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {p q : B.Sorts} (Kp : Kernel B.source p)
    (Kq : Kernel B.source q)
    (hp : originalExactOnCurrentSort A B P transport
      base hOne E p ≤ current_kernel_exact_eq B Kp)
    (hq : originalExactOnCurrentSort A B P transport
      base hOne E q ≤ current_kernel_exact_eq B Kq) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    Arrow B.source Kp Kq ≃
      Arrow Q.source
        (originalCoherentAllparentProjectedKernel
          A B P transport tp base hOne E p Kp hp)
        (originalCoherentAllparentProjectedKernel
          A B P transport tp base hOne E q Kq hq) := by
  dsimp only
  let J := originalExactCurrentKernelFamily
    A B P transport base hOne E
  let W := originalExactCurrentKernelWords
    A B P transport base hOne E
  let hW := originalExactCurrentKernelWords_relation
    A B P transport base hOne E
  let Q := originalExactAllCurrentQuotientCurrentSource
    A B P transport base hOne E
  let π : ∀ i : B.Sorts, B.Point i → Q.Point i :=
    fun _ x => Quotient.mk'' x
  letI : ∀ i : B.Sorts, MulAction B.G (Q.Point i) := Q.action
  have hSurj : ∀ i : B.Sorts, Function.Surjective (π i) := by
    intro i
    exact Quotient.mk''_surjective
  have hEquiv : ∀ i (g : B.G) (x : B.Point i),
      π i (g • x) = g • π i x := by
    intro i g x
    rfl
  have hKernel : ∀ i : B.Sorts,
      GroupActions.kernel (π i) =
        RawExact.evaluate B.source (W i).words := by
    intro i
    exact CCO.SimultaneousQuotients.exact_kernel
      B.source J W hW i
  have hOrbital :
      ∀ {i j : B.Sorts} (x : Q.Point i) (y : Q.Point j)
          (x' : Q.Point i) (y' : Q.Point j),
        Q.source.colour x y = Q.source.colour x' y' ↔
          GroupActions.orbital (G := B.G) x y x' y' := by
    intro i j x y x' y'
    exact CCO.SimultaneousQuotients.actual_colours
      B.source B.homogeneous J W hW x y x' y'
  have hNp : ∀ x y, π p x = π p y → Kp.rel x y := by
    intro x y hxy
    exact hp (Quotient.exact hxy)
  have hNq : ∀ x y, π q x = π q y → Kq.rel x y := by
    intro x y hxy
    exact hq (Quotient.exact hxy)
  have hKp : FullExact Q.source
      (Kp.projectedSetoid (π p) (hSurj p) hNp).r := by
    change FullExact Q.source (Quotient.image (π p) (π p) Kp.rel)
    exact original_coherent_allparent_projected_gate_exact
      A B P transport tp base hOne E p Kp hp
  have hKq : FullExact Q.source
      (Kq.projectedSetoid (π q) (hSurj q) hNq).r := by
    change FullExact Q.source (Quotient.image (π q) (π q) Kq.rel)
    exact original_coherent_allparent_projected_gate_exact
      A B P transport tp base hOne E q Kq hq
  exact Endpoint.arrowEquiv B.source Q.source B.homogeneous B.cco
    π hSurj hEquiv W hKernel hOrbital
    Kp Kq hNp hNq hKp hKq

end
end CCO.ExactEPGeometry
