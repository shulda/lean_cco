import CCO.ExactEPGeometry.OriginalSelectedOccupancyActionMap
import CCO.ExactEPGeometry.OriginalRetainedSelectedGateArrowAction
import CCO.ExactEPGeometry.OriginalNormalizedAnchorPointAction

/-!
# B062 C93: actual selected E-occupancy action is natural for ALL old Arrows

An old reached type b is sent to the literal E-occupancy quotient
object [b]. Its WHOLE K_b-class set is mapped bijectively to the true
selected K_a/E_a-class carrier at the canonical reached anchor a.
An old Arrow R:b->c is first normalized through the genuine whole
G-identity bridges and then sent through the fully surjective C83
old-to-selected Arrow correspondence.

The proof combines:
(1) whole I_ba/I_ab cancellation from actual C79 (all old points);
(2) exact old normalization of the complete Arrow action;
(3) original C82/C83 selected gate-class action naturality.
It checks the ENTIRE groupoid, not just a generator or one orbit.

No quotient SAP, hidden source action section, mixed reverse RAW
descent or new phase axioms. This is the missing naturality premise
for the exact selected-to-old global marking pullback, not yet
the entire finite-age converse C96.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- C93 genuine naturality of the old K-class-to-selected K/E-class
point map for EVERY original complete Reached Arrow R. -/
theorem originalReachedSelectedAction_natural
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    let CB := exactCalculus_of_homogeneous_CCO
      B.source B.homogeneous B.cco
    letI := Reached.groupoid B.homogeneous CB (A := Kroot)
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    ∀ (b c : Reached B.source Kroot) (R : b ⟶ c)
      (q : (Reached.kernel B.homogeneous CB b).Class),
      originalReachedSelectedActionPoint
          A B P transport tp hOne Kroot E hE c
          (R.quotientMap B.homogeneous q) =
        F.map (originalReachedSelectedActionArrow
          A B P transport tp hOne Kroot E hE b c R)
          (originalReachedSelectedActionPoint
            A B P transport tp hOne Kroot E hE b q) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous CB (A := Kroot)
  letI := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  change ∀ (b c : Reached B.source Kroot) (R : b ⟶ c)
    (q : (Reached.kernel B.homogeneous CB b).Class),
      originalReachedSelectedActionPoint
        A B P transport tp hOne Kroot E hE c
        (R.quotientMap B.homogeneous q) =
      F.map (originalReachedSelectedActionArrow
        A B P transport tp hOne Kroot E hE b c R)
        (originalReachedSelectedActionPoint
          A B P transport tp hOne Kroot E hE b q)
  intro b c R q
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let J := originalExactOccupancySetoid A B P base hBase E
  let a := originalReachedOccupancyAnchorOf A B P base hBase E Kroot b
  let d := originalReachedOccupancyAnchorOf A B P base hBase E Kroot c
  let hba : J.r b.val a.val :=
    originalReachedOccupancyAnchorOf_supported
      A B P base hBase E Kroot b
  let hcd : J.r c.val d.val :=
    originalReachedOccupancyAnchorOf_supported
      A B P base hBase E Kroot c
  let Iba := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b a hba
  let Icd := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE c d hcd
  let N := originalRetainedNormalizedArrow
    A B P transport tp hOne Kroot E hE b c R
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
  have hOld :
      N.quotientMap B.homogeneous
        (Iba.quotientMap B.homogeneous q) =
      Icd.quotientMap B.homogeneous
        (R.quotientMap B.homogeneous q) :=
    originalRetainedNormalizedArrow_anchor_action
      A B P transport tp hOne Kroot E hE b c R q
  have hSelected :=
    originalRetainedSelectedGateClass_arrow_natural
      A B P transport tp hOne Kroot E hE a d N
        (Iba.quotientMap B.homogeneous q)
  change (originalRetainedSelectedGateClassEquiv
      A B P transport tp hOne Kroot E hE d)
        (Icd.quotientMap B.homogeneous
          (R.quotientMap B.homogeneous q)) =
    ((originalRetainedSelectedArrowEquiv
      A B P transport tp hOne Kroot E hE a d) N).quotientMap
        Q.homogeneous
        ((originalRetainedSelectedGateClassEquiv
          A B P transport tp hOne Kroot E hE a)
          (Iba.quotientMap B.homogeneous q))
  rw [← hOld]
  exact hSelected

end
end CCO.ExactEPGeometry
