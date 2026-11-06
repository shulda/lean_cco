import CCO.ExactEPGeometry.OriginalAllparentGateClasses
import CCO.ExactEPGeometry.ProjectedGateArrowNaturality

/-!
# B062 C83/C93: TRUE all-parent quotient Arrow actions respect K/E class maps

The actual C67 AP+HOM CCO simultaneous typed E-quotient and the C82
genuine projected full-RAW exact endpoint gates carry EVERY whole
old Arrow, under the actual proven C83 full Hom equivalence.
The canonical K-class ↔ (K/E)-class bijections commute with these
complete Arrow quotient maps. This is not just agreement on one
generator or arbitrary source data; the quotient Arrow is the
genuinely pushed FULL old relation.

Retyping all parent E-class carriers to one canonical E-occupancy
sort and normalizing duplicate reached objects are separate later
steps. No quotient SAP or group-action section is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Naturality of the real C82 original-to-all-parent K/E class
equivalence for EVERY actual C83 quotient Arrow. -/
theorem originalAllparentGateClass_arrow_natural
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {p q : B.Sorts} (Kp : Kernel B.source p) (Kq : Kernel B.source q)
    (hp : originalExactOnCurrentSort A B P transport
      base hOne E p ≤ current_kernel_exact_eq B Kp)
    (hq : originalExactOnCurrentSort A B P transport
      base hOne E q ≤ current_kernel_exact_eq B Kq)
    (R : Arrow B.source Kp Kq) :
    let Q := originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
    ∀ x : Kp.Class,
      originalAllparentGateClassEquiv
          A B P transport tp base hOne E q Kq hq
          (R.quotientMap B.homogeneous x) =
        ((originalCoherentAllparentArrowEquiv
          A B P transport tp base hOne E Kp Kq hp hq) R).quotientMap
          Q.homogeneous
          (originalAllparentGateClassEquiv
            A B P transport tp base hOne E p Kp hp x) := by
  let Q : CurrentSource.{u,v,v,t} :=
    originalExactAllCurrentQuotientCurrentSource
      A B P transport base hOne E
  letI : ∀ i : Q.Sorts, MulAction Q.G (Q.Point i) := Q.action
  let pi : ∀ i : B.Sorts, B.Point i → Q.Point i :=
    fun _ x => Quotient.mk'' x
  have hNp : ∀ x y, pi p x = pi p y → Kp.rel x y := by
    intro x y h
    exact hp (Quotient.exact h)
  have hNq : ∀ x y, pi q x = pi q y → Kq.rel x y := by
    intro x y h
    exact hq (Quotient.exact h)
  have hExactP : FullExact Q.source
      (Kp.projectedSetoid (pi p) Quotient.mk''_surjective hNp).r := by
    change FullExact Q.source (Quotient.image (pi p) (pi p) Kp.rel)
    exact original_coherent_allparent_projected_gate_exact
      A B P transport tp base hOne E p Kp hp
  have hExactQ : FullExact Q.source
      (Kq.projectedSetoid (pi q) Quotient.mk''_surjective hNq).r := by
    change FullExact Q.source (Quotient.image (pi q) (pi q) Kq.rel)
    exact original_coherent_allparent_projected_gate_exact
      A B P transport tp base hOne E q Kq hq
  let U : Arrow Q.source
      (Kp.projectedKernel Q.source (pi p)
        Quotient.mk''_surjective hNp hExactP)
      (Kq.projectedKernel Q.source (pi q)
        Quotient.mk''_surjective hNq hExactQ) :=
    (originalCoherentAllparentArrowEquiv
      A B P transport tp base hOne E Kp Kq hp hq) R
  have hImage : ∀ x y, R.rel x y → U.rel (pi p x) (pi q y) := by
    intro x y hr
    change Quotient.image (pi p) (pi q) R.rel (pi p x) (pi q y)
    exact ⟨x,y,rfl,rfl,hr⟩
  change ∀ x : Kp.Class,
    projectedGateClassMap Kq (pi q) Quotient.mk''_surjective hNq
        (R.quotientMap B.homogeneous x) =
      U.quotientMap Q.homogeneous
        (projectedGateClassMap Kp (pi p) Quotient.mk''_surjective hNp x)
  intro x
  induction x using Quotient.inductionOn with
  | _ x =>
    let y := R.pointImage B.homogeneous x
    have hr : R.rel x y := R.pointImage_spec B.homogeneous x
    have hu : U.rel (pi p x) (pi q y) := hImage x y hr
    have hq :
        U.quotientMap Q.homogeneous
          ((Kp.projectedKernel Q.source (pi p)
            Quotient.mk''_surjective hNp hExactP).project (pi p x)) =
        (Kq.projectedKernel Q.source (pi q)
          Quotient.mk''_surjective hNq hExactQ).project (pi q y) :=
      (U.quotientMap_eq_iff Q.homogeneous (pi p x) (pi q y)).mpr hu
    change U.quotientMap Q.homogeneous (Quotient.mk'' (pi p x)) =
      Quotient.mk'' (pi q y) at hq
    change projectedGateClassMap Kq (pi q) Quotient.mk''_surjective hNq
        (R.quotientMap B.homogeneous (Kp.project x)) =
      U.quotientMap Q.homogeneous
        (projectedGateClassMap Kp (pi p) Quotient.mk''_surjective hNp
          (Kp.project x))
    rw [R.quotientMap_project B.homogeneous x]
    change Quotient.mk'' (pi q y) =
      U.quotientMap Q.homogeneous (Quotient.mk'' (pi p x))
    exact hq.symm

end
end CCO.ExactEPGeometry
