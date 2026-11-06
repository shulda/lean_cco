import CCO.ExactEPGeometry.OriginalSelectedGlobalEClassEquiv
import CCO.ExactEPGeometry.OriginalGlobalEclassHistory
import CCO.ExactEPGeometry.OriginalDiscardedOccupancyQuotientEquiv
import CCO.ExactEPGeometry.CanonicalStepExact

/-!
# B062 C103: actual selected E-points and their discarded occupancy names

The actual selected quotient points at a true character step are bijective
through their literal global original-E classes. For a discarded step this
same point map has EXACTLY the already proved occupancy-sort equivalence as
owner map. No choice of an automorphism or group section occurs.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

variable (A B : CurrentSource.{u,v,w,t})
variable (P : UnaryReduct A.source B.source)
variable (transport : ExactTraceTransport A.source B.source P)
variable {r : B.Sorts} (Kroot : Kernel B.source r)
variable (phase : SourcePhase B.source B.homogeneous
  (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
variable (base : A.Sorts) (hOne : ∀ i : A.Sorts, base = i)
variable (E : ExactEq A.source base)

/-- The true selected quotient point bijection at ANY actual character
step. All exact transport for the successor is constructed internally. -/
def originalPhaseSelectedPointEquiv :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    Sigma (originalExactSelectedQuotientCurrentSource
      A N (P.compose R) hN base hOne E).Point ≃
    Sigma (originalExactSelectedQuotientCurrentSource
      A B P transport base hOne E).Point :=
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  (originalSelectedGlobalEClassEquiv A N (P.compose R) hN base hOne E).trans
    ((originalGlobalEclassEquivAlongReduct A B N P R base hOne E).trans
      (originalSelectedGlobalEClassEquiv A B P transport base hOne E).symm)

/-- The map is characterized by its literal global original-E class. -/
theorem originalPhaseSelectedPointEquiv_globalE
    (q : Sigma (originalExactSelectedQuotientCurrentSource
      A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
      (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
        (canonical_step_exact_transport B phase)) base hOne E).Point) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
    let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hOne E
    let repB := originalSelectedTaggedRepresentative A B P transport base hOne E
    (currentOriginalExactSetoid A B P base hOne E).r
      (repB (originalPhaseSelectedPointEquiv A B P transport Kroot phase base hOne E q))
      (R.project (repN q)) := by
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let eB := originalSelectedGlobalEClassEquiv A B P transport base hOne E
  let eN := originalSelectedGlobalEClassEquiv A N (P.compose R) hN base hOne E
  let eR := originalGlobalEclassEquivAlongReduct A B N P R base hOne E
  have h : eB (originalPhaseSelectedPointEquiv A B P transport Kroot phase base hOne E q) =
      eR (eN q) := eB.apply_symm_apply _
  change (Quotient.mk'' (originalSelectedTaggedRepresentative A B P transport base hOne E
      (originalPhaseSelectedPointEquiv A B P transport Kroot phase base hOne E q)) :
      Quotient (currentOriginalExactSetoid A B P base hOne E)) =
    Quotient.mk'' (R.project (originalSelectedTaggedRepresentative A N (P.compose R) hN base hOne E q)) at h
  exact Quotient.exact h

end

noncomputable section

/-- At a discarded step, the true selected point bijection lies over the
actual occupancy-sort equivalence, rather than an arbitrary retyping. -/
theorem originalDiscardedSelectedPointEquiv_owner
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (q : Sigma (originalExactSelectedQuotientCurrentSource
      A (SingleStep.successor B phase) (P.compose (SingleStep.projection B phase))
      (ExactTraceTransport.compose P (SingleStep.projection B phase) transport
        (canonical_step_exact_transport B phase)) (P.parent r)
      (fun i => hOne (P.parent r) i) E).Point) :
    (originalPhaseSelectedPointEquiv A B P transport Kroot phase (P.parent r)
      (fun i => hOne (P.parent r) i) E q).1 =
    originalDiscardedOccupancySortClassEquiv A B P transport tp hOne Kroot phase E hNot q.1 := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let N := SingleStep.successor B phase
  let R := SingleStep.projection B phase
  let hN := ExactTraceTransport.compose P R transport (canonical_step_exact_transport B phase)
  let f := originalPhaseSelectedPointEquiv A B P transport Kroot phase base hBase E
  let e := originalDiscardedOccupancySortClassEquiv A B P transport tp hOne Kroot phase E hNot
  let repN := originalSelectedTaggedRepresentative A N (P.compose R) hN base hBase E
  let repB := originalSelectedTaggedRepresentative A B P transport base hBase E
  have hE := originalPhaseSelectedPointEquiv_globalE
    A B P transport Kroot phase base hBase E q
  have hSupport : (originalExactOccupancySetoid A B P base hBase E).r
      (repB (f q)).1 (R.project (repN q)).1 :=
    ⟨(repB (f q)).2,(R.project (repN q)).2,hE⟩
  change (f q).1 = e q.1
  have hB := originalOccupancyRepresentative_class A B P base hBase E (f q).1
  have hNclass := originalOccupancyRepresentative_class A N (P.compose R) base hBase E q.1
  have hMap : (Quotient.mk'' (R.project (repN q)).1 : OriginalOccupancy A B P base hBase E) =
      e (Quotient.mk'' (repN q).1 : OriginalOccupancy A N (P.compose R) base hBase E) := rfl
  exact hB.symm.trans ((Quotient.sound hSupport).trans (hMap.trans (congrArg e hNclass)))

end
end CCO.ExactEPGeometry
