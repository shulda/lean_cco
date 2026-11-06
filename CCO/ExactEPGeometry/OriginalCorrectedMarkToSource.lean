import CCO.ExactEPGeometry.OriginalGaugeMarkingTransfer
import CCO.APCharacter.ActualMasks

/-!
# B062 C93/C95: actual corrected full Reached marking gives old global source mark

The original C84 objectwise phase correction is constructed from the
actual old E-occupancy gate bridges. Any full marking for this
gauge-corrected original reached-groupoid character therefore gives
a full marking for the genuine original SourcePhase character by the
proved inverse gauge equation. The accepted AP-only original-marking
provider then supplies a globally legal bit function on ALL actual
old source points, including the inactive sorts with their forced
zero bits.

Every reached old point has the precise original seed value
(corrected marking on its K-class + its genuine original C79 offset).
No quotient SAP, automorphism section, arbitrary future quotient
limit, or assumed marked source is introduced.

To finish C93, the separately constructed SELECTED E-quotient
groupoid marking must still be transported naturally to this
corrected original reached action. That transfer is NOT assumed here.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- Actual old globally legal phase marking from an arbitrary
globally compatible corrected marking of the WHOLE original
reached groupoid, with explicit all-parent/old-offset evaluation. -/
theorem originalCorrectedMarkToOldSource
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
      (current_kernel_exact_eq B Kroot)) :
    let C := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    letI := Reached.groupoid B.homogeneous C (A := Kroot)
    let F := Reached.pointFunctor B.homogeneous C Kroot
    let gamma := originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE
    ∀ (mark : Abstract.Point F → ZMod 2),
      Abstract.IsMarking F
        (originalReachedGlobalCharacter A B P transport tp
          hOne Kroot phase E hE) mark →
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ (b : Reached B.source Kroot) (x : B.Point b.val),
            oldMark ⟨b.val,x⟩ =
              mark ⟨b,(Reached.kernel B.homogeneous C b).project x⟩ +
                gamma b := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous C (A := Kroot)
  let F := Reached.pointFunctor B.homogeneous C Kroot
  let gamma := originalReachedGlobalOffset A B P transport tp
    hOne Kroot phase E hE
  change ∀ (mark : Abstract.Point F → ZMod 2),
      Abstract.IsMarking F
        (originalReachedGlobalCharacter A B P transport tp
          hOne Kroot phase E hE) mark →
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ (b : Reached B.source Kroot) (x : B.Point b.val),
            oldMark ⟨b.val,x⟩ =
              mark ⟨b,(Reached.kernel B.homogeneous C b).project x⟩ +
                gamma b
  intro mark hm
  let oldGroupMark : Abstract.Point F → ZMod 2 :=
    gaugeMarking F gamma mark
  have hOldGroup : Abstract.IsMarking F phase.character oldGroupMark :=
    originalReachedCorrectedMarking_toOriginal
      A B P transport tp hOne Kroot phase E hE mark hm
  let oldMark := originalMarking B.source B.homogeneous C Kroot oldGroupMark
  refine ⟨oldMark,phase.original_global_marking oldGroupMark hOldGroup,?_⟩
  intro b x
  change originalMarking B.source B.homogeneous C Kroot
      oldGroupMark ⟨b.val,x⟩ =
    oldGroupMark ⟨b,(Reached.kernel B.homogeneous C b).project x⟩
  exact originalMarking_reached B.source B.homogeneous C Kroot oldGroupMark b x

end
end CCO.ExactEPGeometry
