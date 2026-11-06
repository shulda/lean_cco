import CCO.ExactEPGeometry.OriginalRetainedMixedActiveMarkedChart
import CCO.ExactEPGeometry.OriginalRetainedMixedSelectedInjectivity

/-!
# B062 C96: one genuine mixed selected E-quotient marked-age chart

Starting with an arbitrary finite family of DISTINCT ACTUALLY
REALIZED selected E-quotient prefix points, reached or inactive,
we use the actual C84 full-arrow mask equations on the active
points to construct one old global marking. The inactive selected
points use the genuine forced-zero phase.

Previously the mixed old marked-age chart required independent
injectivity of its chosen fine old representatives. The real C90
reached E-class right inverses, C66 canonical inactive E-class
representatives and disjoint reached/inactive old sorts PROVE that
injectivity from distinctness of the actual quotient vertices.

The output is an embedding into the ACTUAL AP-only homogeneous
marked successor with all OLD fine orbital names preserved.
No quotient SAP, group section, or new source provider is assumed.
Still open: arbitrary previously UNREALIZED quotient orbital diagram
realization and identification of the COMPLETE marked quotient
atomic palette/age in C96/C103.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory
open OwnerTransversal.CountableColour

noncomputable section

/-- C96, reached plus inactive actual selected-E-quotient vertices:
full Arrow character masks and distinctness of the TRUE quotient
vertices suffice for a real mixed old fine-colour marked chart.
There is no additional old representative injectivity hypothesis. -/
theorem originalRetainedMixedSelectedMasks_oldMarkedChart
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
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    letI := originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource
      A B P transport base hBase E
    let anchor := originalReachedOccupancyAnchor
      A B P base hBase E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (n m : Nat)
      (owners : Fin n → Occ)
      (points : ∀ i : Fin n,
        Q.Point (Quotient.mk'' (anchor (owners i)).val))
      (bits : Fin n → ZMod 2),
      (∀ i j : Fin n,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (points i) (points j))
          (bits i) (bits j)) →
      ∀ (inactivePoints : Fin m → Sigma Q.Point),
        Function.Injective (fun v : Sum (Fin n) (Fin m) =>
          match v with
          | Sum.inl i =>
              (⟨(Quotient.mk'' (anchor (owners i)).val :
                OriginalOccupancy A B P base hBase E),points i⟩ :
                Sigma Q.Point)
          | Sum.inr j => inactivePoints j) →
        (∀ j : Fin m,
          ¬Nonempty (Bridge B.source Kroot
            (originalSelectedTaggedRepresentative
              A B P transport base hBase E (inactivePoints j)).1)) →
        let old : Sum (Fin n) (Fin m) → Sigma B.Point :=
          fun v => match v with
          | Sum.inl i =>
              ⟨(anchor (owners i)).val,
                originalSelectedReachedEclassRepresentative
                  A B P transport hOne Kroot E
                    (anchor (owners i)) (points i)⟩
          | Sum.inr j =>
              originalSelectedTaggedRepresentative
                A B P transport base hBase E (inactivePoints j)
        let allBits : Sum (Fin n) (Fin m) → ZMod 2 :=
          fun v => match v with
          | Sum.inl i => bits i
          | Sum.inr _ => 0
        ∃ f : Sum (Fin n) (Fin m) ↪ phase.MarkedLimit B.cco,
          (∀ v, (phase.markedCoding B.cco).table.owner (f v) =
            APCharacter.Age.ownerEquiv B.source
              ((old v).1,allBits v)) ∧
          ∀ v w, (phase.markedCoding B.cco).table.colour (f v) (f w) =
            APCharacter.Age.colourEquiv B.source
              (taggedColour B.source (old v) (old w)) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport base hBase E
  let anchor := originalReachedOccupancyAnchor
    A B P base hBase E Kroot
  let K := fun o : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor o)
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  dsimp only
  intro n m owners points bits hMasks inactivePoints hSelected hInactive
  let old : Sum (Fin n) (Fin m) → Sigma B.Point :=
    fun v => match v with
    | Sum.inl i =>
        ⟨(anchor (owners i)).val,
          originalSelectedReachedEclassRepresentative
            A B P transport hOne Kroot E
              (anchor (owners i)) (points i)⟩
    | Sum.inr j =>
        originalSelectedTaggedRepresentative
          A B P transport base hBase E (inactivePoints j)
  have hOldInj : Function.Injective old :=
    originalRetainedMixedSelectedOld_injective
      A B P transport hOne Kroot E
        n m owners points inactivePoints hSelected hInactive
  exact originalRetainedMixedActiveMasks_oldMarkedChart
    A B P transport tp hOne Kroot phase E hE
      n m owners points bits hMasks old
        (fun i => rfl) (fun j => hInactive j) hOldInj

end
end CCO.ExactEPGeometry
