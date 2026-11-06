import CCO.ExactEPGeometry.OriginalRetainedSelectedReached
import CCO.RigidGroupoid.Geometry.Transport

/-!
# B062 C103: actual selected full-arrow dominance

For every original reached gate, every genuine strictly larger full RAW
selected equivalence pulls back to a strictly larger original current
equivalence. Thus any actual dominant old loop has a dominant whole selected
image. All-parent FullExact pullback and surjectivity are source-constructed;
there is no extra quotient-dominance premise.
-/

universe u v w t
namespace CCO.ExactEPGeometry
open APCharacter.Towers RigidGroupoid.Geometry
noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable (tp : ExactTraceProduct A.source B.source P)
variable (hOne : ∀ i j : A.Sorts, i = j)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (E : ExactEq A.source (P.parent r))
variable (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
  (current_kernel_exact_eq B Kroot))

/-- Actual dominance against ALL genuine original full RAW selected
equivalences, not only a separately chosen interval or atom family. -/
theorem originalRetainedSelectedArrow_dominant
    (b : Reached B.source Kroot)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b))
    (hR : Dominant (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b) R) :
    Dominant (originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE b)
      ((originalRetainedSelectedArrowEquiv A B P transport tp hOne Kroot E hE b b) R) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  let Kq := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE b
  letI : PartialOrder (Kernel B.source b.val) := kernelPartialOrder B.source b.val
  letI : PartialOrder (Kernel Q.source
      (Quotient.mk'' b.val : OriginalOccupancy A B P base hBase E)) :=
    kernelPartialOrder Q.source _
  let pi := originalSelectedLocalProjection A B P transport base hBase E b.val
  have hSurj : Function.Surjective pi :=
    originalSelectedLocalProjection_surjective A B P transport base hBase E b.val
  have hPull := originalRetainedSelectedKernel_parentPullback
    A B P transport tp hOne Kroot E hE b
  intro Z hStrict p q hOdd
  let W := originalExactSelectedAtParentKernelPullback A B P transport base hBase E Z
  have hOldLE : K ≤ W := by
    intro x y hK
    have hProjected : Kq.rel (pi x) (pi y) := by
      change (originalExactSelectedAtParentKernelPullback A B P transport base hBase E Kq).rel x y
      rw [hPull]
      exact hK
    exact hStrict.le hProjected
  have hOldStrict : K < W := by
    refine lt_iff_le_and_ne.mpr ⟨hOldLE,?_⟩
    intro heq
    have hZle : Z ≤ Kq := by
      intro u v hZ
      obtain ⟨x,rfl⟩ := hSurj u
      obtain ⟨y,rfl⟩ := hSurj v
      have hW : W.rel x y := hZ
      have hK : K.rel x y := by rw [heq]; exact hW
      change (originalExactSelectedAtParentKernelPullback A B P transport base hBase E Kq).rel x y
      rw [hPull]
      exact hK
    exact (not_le_of_gt hStrict) hZle
  obtain ⟨x,rfl⟩ := hSurj p
  obtain ⟨y,rfl⟩ := hSurj q
  have hOld : R.rel x y :=
    (originalRetainedSelectedArrow_real_pair_iff
      A B P transport tp hOne Kroot E hE b b R x y).mp hOdd
  exact hR W hOldStrict x y hOld

end
end CCO.ExactEPGeometry
