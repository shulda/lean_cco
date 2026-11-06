import CCO.ExactEPGeometry.OriginalSelectedParentPullback
import CCO.ExactEPGeometry.OriginalRetainedSelectedArrowRealPair
import CCO.ExactEPGeometry.OriginalRetainedSelectedArrowUnits

/-!
# B062 C103: the COMPLETE actually reached selected quotient objects

The arbitrary-parent exact pullback recovers the original current gate
from the projected selected gate. Therefore EVERY full bridge from the
true selected root pulls back to a full bridge from the true old root.
Conversely EVERY actually old-reached object has its whole connecting
arrow projected by the proved full Hom equivalence. Thus the actual
selected Reached set has precisely the retained occupancy components;
no additional reached-sort provider or group section is supplied.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter.Towers
open RigidGroupoid.Geometry

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

/-- The whole selected gate pulls back to PRECISELY the corresponding
true current full gate at every reached old parent, including the root. -/
theorem originalRetainedSelectedKernel_parentPullback
    (b : Reached B.source Kroot) :
    originalExactSelectedAtParentKernelPullback A B P transport (P.parent r)
      (fun i => hOne (P.parent r) i) E
      (originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE b) =
    Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) b := by
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  apply kernel_ext B.source
  apply Setoid.ext
  intro x y
  have h := originalRetainedSelectedArrow_real_pair_iff
    A B P transport tp hOne Kroot E hE b b (Arrow.id Kb) x y
  dsimp only at h
  have hid := originalRetainedSelectedArrow_id A B P transport tp hOne Kroot E hE b
  erw [hid] at h
  exact h

/-- The actual selected quotient has a FULL bridge to [j] EXACTLY when
the old current source has a FULL bridge to j. This quantifies over ALL
selected bridges, including those not supplied by the forward Hom map. -/
theorem originalRetainedSelectedReached_iff
    (j : B.Sorts) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
    Nonempty (Bridge Q.source KQ (Quotient.mk'' j : OriginalOccupancy A B P base hBase E)) ↔
      Nonempty (Bridge B.source Kroot j) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let C := exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco
  let KQ := originalRetainedSelectedKernel A B P transport tp hOne Kroot E hE (Reached.root Kroot)
  have hRootPull : originalExactSelectedAtParentKernelPullback A B P transport base hBase E KQ = Kroot :=
    (originalRetainedSelectedKernel_parentPullback
      A B P transport tp hOne Kroot E hE (Reached.root Kroot)).trans
      (Reached.root_kernel B.homogeneous C (A := Kroot))
  constructor
  · rintro ⟨R⟩
    have old := originalExactSelectedAtParentsBridgePullback A B P transport base hBase E KQ R
    exact ⟨hRootPull ▸ old⟩
  · intro hOld
    let b : Reached B.source Kroot := ⟨j,hOld⟩
    let R := Reached.connectingArrow B.homogeneous C (Reached.root Kroot) b
    exact ⟨((originalRetainedSelectedArrowEquiv
      A B P transport tp hOne Kroot E hE (Reached.root Kroot) b) R).toBridge⟩

end
end CCO.ExactEPGeometry
