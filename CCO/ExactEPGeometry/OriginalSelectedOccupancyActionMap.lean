import CCO.ExactEPGeometry.OriginalReachedToSelectedPoints
import CCO.ExactEPGeometry.OriginalRetainedSelectedNormalizedCharacter
import CCO.ExactEPGeometry.OriginalRetainedSelectedPointAction

/-!
# B062 C84/C93: the ACTUAL original reached action maps into selected occupancy

The true E-occupancy quotient of old reached objects has one chosen
anchor per component. Every whole original reached Arrow R:b->c is
normalized via original G-identity transports I_(a_b,b) and
I_(c,a_c), and mapped by the COMPLETE C83 Hom equivalence into a
whole selected E-quotient Arrow between the canonical anchor gates.

Old K_b classes are transported by the genuine whole I_(b,a_b)
quotientMap and the real class bijection K_a ≃ K_a/E_a of C82/C83.
No synthetic quotient point, new group action or automorphism-group
section is used.

The exact C84 character identity is proved here. Naturality of all
the actions and consequent marking pullback are separate consumers.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- For EVERY actual original reached full Arrow, its selected
E-occupancy image is a WHOLE projected Arrow normalized at the
true occupancy anchors. The old and selected groupoid object
sets are different and are not silently identified. -/
noncomputable def originalReachedSelectedActionArrow
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) c)) :
    let Occ := OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    (Quotient.mk'' b : Occ) ⟶ (Quotient.mk'' c : Occ) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  letI := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  let anchor := originalReachedOccupancyAnchorOf
    A B P base hBase E Kroot
  exact (originalRetainedSelectedArrowEquiv
    A B P transport tp hOne Kroot E hE
      (anchor b) (anchor c))
    (originalRetainedNormalizedArrow
      A B P transport tp hOne Kroot E hE b c R)

/-- At each old Reached object, the source point-action carrier maps
bijectively to the TRUE projected selected gate-class carrier
of its single canonical E-occupancy object. -/
noncomputable def originalReachedSelectedActionPoint
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot) :
    let Occ := OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).Class →
      F.obj (Quotient.mk'' b : Occ) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  letI := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  change (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).Class →
    (originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE
      (originalReachedOccupancyAnchorOf A B P base hBase E Kroot b)).Class
  exact (originalReachedSelectedPointEquiv
    A B P transport tp hOne Kroot E hE b).toFun

/-- Exact complete C84 character correction on EVERY original old
source Arrow, after true E-occupancy normalization. The source
old phase remains the actual SourcePhase character. -/
theorem originalReachedSelectedActionArrow_character
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
      (current_kernel_exact_eq B Kroot))
    (b c : Reached B.source Kroot)
    (R : Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b)
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) c)) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    (originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE).value
      (originalReachedSelectedActionArrow
        A B P transport tp hOne Kroot E hE b c R) =
      originalReachedGlobalOffset A B P transport tp
        hOne Kroot phase E hE b +
      phase.character.value R +
      originalReachedGlobalOffset A B P transport tp
        hOne Kroot phase E hE c := by
  letI := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
  calc
    (originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE).value
      (originalReachedSelectedActionArrow
        A B P transport tp hOne Kroot E hE b c R) =
      (originalReachedGlobalCharacter A B P transport tp
        hOne Kroot phase E hE).value R :=
      originalRetainedSelectedNormalized_character_value
        A B P transport tp hOne Kroot phase E hE b c R
    _ = originalReachedGlobalOffset A B P transport tp
          hOne Kroot phase E hE b +
        phase.character.value R +
        originalReachedGlobalOffset A B P transport tp
          hOne Kroot phase E hE c := rfl

end
end CCO.ExactEPGeometry
