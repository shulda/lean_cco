import CCO.ExactEPGeometry.OriginalSelectedAnchorActionReadout
import CCO.ExactEPGeometry.OriginalSelectedReachedPointLifts
import CCO.ExactEPGeometry.OriginalSelectedFullMarkToOld

/-!
# B062 C93–C95: exact pointwise bits at true selected E-occupancy anchors

An actual full selected E-quotient groupoid marking is pulled back to a
single globally legal original SourcePhase marking by the proven full
Arrow-action naturality and C79/C84 objectwise character correction.

This theorem additionally evaluates that old marking at the actual
old point representing EVERY selected quotient E-class at a reached
occupancy anchor. The result is precisely the original prescribed
selected K/E marking bit, with NO shift: C79 proves gamma(anchor)=0.
The selected E-class itself, not just some other point in its K/E gate
class, has a genuine old representative from C49/C66. The whole
identity gate acts trivially by C79, never by pretending K/E is logical
equality.

All original old sort mask conditions hold, including inactive sorts
with their actual zero bit. This concerns already realized selected
E-quotient prefix points; realization of arbitrary locally admissible
unmarked quotient-prefix diagrams and the complete finite marked-age
converse are still separate original C89–C96 obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- A SINGLE genuine globally legal old marking realizes the
prescribed bit at EVERY selected original E-class on an active
occupancy anchor, for any true full selected-character marking.
The zero correction at the actual reached anchor is proved, not
assumed. -/
theorem originalSelectedFullMark_exactAnchorBits
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
    let Occ := OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport (P.parent r)
        (fun i => hOne (P.parent r) i) E
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    let anchor := originalReachedOccupancyAnchor
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    ∀ (selectedMark : Abstract.Point F → ZMod 2),
      Abstract.IsMarking F chi selectedMark →
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ (o : Occ) (q : Q.Point (Quotient.mk'' (anchor o).val)),
            oldMark ⟨(anchor o).val,
              originalSelectedReachedEclassRepresentative
                A B P transport hOne Kroot E (anchor o) q⟩ =
            selectedMark (⟨o,(K o).project q⟩ : Abstract.Point F) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous CB (A := Kroot)
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport (P.parent r)
      (fun i => hOne (P.parent r) i) E
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  let anchor := originalReachedOccupancyAnchor
    A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
  let K := fun o : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor o)
  let gamma := originalReachedGlobalOffset
    A B P transport tp hOne Kroot phase E hE
  change ∀ (selectedMark : Abstract.Point F → ZMod 2),
      Abstract.IsMarking F chi selectedMark →
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ (o : Occ) (q : Q.Point (Quotient.mk'' (anchor o).val)),
            oldMark ⟨(anchor o).val,
              originalSelectedReachedEclassRepresentative
                A B P transport hOne Kroot E (anchor o) q⟩ =
            selectedMark (⟨o,(K o).project q⟩ : Abstract.Point F)
  intro selectedMark hSelected
  obtain ⟨oldMark,hLegal,hValues⟩ :=
    originalSelectedFullMarkToOldSource
      A B P transport tp hOne Kroot phase E hE selectedMark hSelected
  refine ⟨oldMark,hLegal,?_⟩
  intro o q
  let a := anchor o
  let Ka := Reached.kernel B.homogeneous CB a
  let x := originalSelectedReachedEclassRepresentative
    A B P transport hOne Kroot E a q
  have hClass : (Quotient.mk'' a : Occ) = o :=
    originalReachedOccupancyAnchor_class
      A B P (P.parent r) (fun i => hOne (P.parent r) i)
      E Kroot o
  have hAnchorMark : HEq
      (originalReachedSelectedActionPoint
        A B P transport tp hOne Kroot E hE a (Ka.project x))
      ((K o).project q) := by
    have hAnchor := originalReachedSelectedActionPoint_anchor_heq
      A B P transport tp hOne Kroot E hE o (Ka.project x)
    have hRepresentative := originalSelectedReachedEclassRepresentative_gate
      A B P transport tp hOne Kroot E hE a q
    exact hAnchor.trans (heq_of_eq hRepresentative)
  have hPoint :
      (⟨(Quotient.mk'' a : Occ),
        originalReachedSelectedActionPoint
          A B P transport tp hOne Kroot E hE a (Ka.project x)⟩ :
          Abstract.Point F) =
      (⟨o,(K o).project q⟩ : Abstract.Point F) := by
    exact Sigma.ext hClass hAnchorMark
  have hZero : gamma a = 0 :=
    originalReachedGlobalOffset_anchor_zero
      A B P transport tp hOne Kroot phase E hE o
  have hv := hValues a x
  change oldMark ⟨a.val,x⟩ =
    selectedMark ⟨(Quotient.mk'' a : Occ),
      originalReachedSelectedActionPoint
        A B P transport tp hOne Kroot E hE a (Ka.project x)⟩ +
      gamma a at hv
  calc
    oldMark ⟨a.val,x⟩ =
      selectedMark (⟨(Quotient.mk'' a : Occ),
        originalReachedSelectedActionPoint
          A B P transport tp hOne Kroot E hE a (Ka.project x)⟩ :
          Abstract.Point F) + gamma a := hv
    _ = selectedMark (⟨o,(K o).project q⟩ :
          Abstract.Point F) + gamma a := by rw [hPoint]
    _ = selectedMark (⟨o,(K o).project q⟩ :
          Abstract.Point F) := by rw [hZero,add_zero]

end
end CCO.ExactEPGeometry
