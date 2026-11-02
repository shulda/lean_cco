import CCO.ExactEPGeometry.OriginalRetainedSelectedPointAction

/-!
# B062 C87–C92: genuine selected K/E action masks and duplicate points

For the ACTUAL one-object-per-original-E-occupancy quotient source,
the previous C83/C84 proofs provide the WHOLE exact Arrow groupoid,
its phase character and its faithful action on the literal gate
classes K/E. This file instantiates the existing finite-character
theorems on that source, without assuming quotient SAP, choosing an
automorphism-group section or replacing complete orbitals by
generating arrows.

The rigid pair readout is an ACTUAL pair of groupoid points and a
genuine full Arrow transporting them. For different true action
orbits, BOTH prescribed phase differences extend to complete global
markings. A duplicate-gate-point argument proves the C92 consistency
requirement: a pairwise compatible finite prescription cannot assign
different bits to two occurrences of the SAME actual K/E point.

This is the actual point-action part of C87–C93; correspondence with
all finite locally allowed quotient diagrams and the true next
marked-age realization are still separate source obligations.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- C87–C88: for every real selected full rigid-groupoid arrow
carrying one actual projected K/E point to another, ALL genuine
character markings have precisely the source-character bit
difference. This is not a statement about a chosen generator. -/
theorem originalRetainedSelectedRigidDifference
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
    :
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (mark : Abstract.Point F → ZMod 2)
      (hm : Abstract.IsMarking F chi mark)
      {a b : OriginalReachedOccupancy A B P (P.parent r)
        (fun k => hOne (P.parent r) k) E Kroot}
      (R : a ⟶ b) (q : F.obj a),
      mark ⟨b,F.map R q⟩ - mark ⟨a,q⟩ = chi.value R := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  intro mark hm a b R q
  exact Abstract.rigid_difference F chi hm R q

/-- C87–C88: if two actual projected K/E points belong to
DIFFERENT orbits of the full selected quotient groupoid action,
BOTH possible bit differences have compatible global markings.
These are full old-source-free-action witnesses, not independent
phase choices inside a rigid orbit. -/
theorem originalRetainedSelectedNonrigidBothDifferences
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
    :
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (p q : Abstract.Point F),
      ¬ Abstract.Orbit F p q →
      ∀ delta : ZMod 2,
        ∃ mark, Abstract.IsMarking F chi mark ∧
          mark q = mark p + delta := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  intro p q hNonrigid delta
  exact Abstract.different_orbits_both_differences F
    (originalRetainedSelectedPointFunctor_free
      A B P transport tp hOne Kroot E hE)
    chi p q hNonrigid delta

/-- C92: duplicate presentations of a literal selected quotient
gate point must have the SAME bit if their finite prescription
obeys all real full-arrow pair constraints. The proof uses the
actual complete GROUPoid gate identity (not quotient equality
on original points), with character ZERO. -/
theorem originalRetainedSelectedDuplicateBit
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
    :
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let F := originalRetainedSelectedPointFunctor
      A B P transport tp hOne Kroot E hE
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (p q : Abstract.Point F) (x y : ZMod 2),
      p = q →
      (∀ R : p.1 ⟶ q.1,
        F.map R p.2 = q.2 → y = x + chi.value R) →
      x = y := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let F := originalRetainedSelectedPointFunctor
    A B P transport tp hOne Kroot E hE
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  intro p q x y hpq hLocal
  subst q
  have h := hLocal (𝟙 p.1) (F.map_id_apply p.1 p.2)
  rw [chi.map_id,add_zero] at h
  exact h.symm

end
end CCO.ExactEPGeometry
