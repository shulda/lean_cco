import CCO.ExactEPGeometry.OriginalActualNextQuotientChart
import CCO.ExactEPGeometry.OriginalRetainedMixedActualNextQuotientChart
import CCO.ExactEPGeometry.OriginalRetainedSelectedFiniteActiveAgeIff

/-!
# B062 C96: both finite-age directions on every mixed selected tuple

For any finite genuine selected quotient configuration, full corrected
character masks are equivalent to a concrete chart in the ACTUAL next
quotient, including genuine inactive vertices and distinct original
E-classes. Every new atomic block of this chart is classified by
`OriginalActualNextQuotientChart.newAtomicPalette`.

The reverse implication reads old local legality from the actual output.
The actual SourcePhase finite-seed extension then gives one global old
marking on the complete finite chart. Its bits on the true reached
E-class representatives imply all complete quotient Arrow masks.
No homogeneity of a seed marking or quotient SAP is used.

This theorem still starts with an arbitrary already realized unmarked
selected tuple. Realization of an arbitrary unmarked quotient diagram
uses the separately proved full actual quotient triangle-age theorem.
-/

universe u v w t
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry
open CategoryTheory

noncomputable section

/-- All corrected active masks, with truly inactive zero labels, are
equivalent to an actual mixed successor quotient chart. Its full NEW
atomic palette is available without additional mathematical hypotheses. -/
theorem originalRetainedMixedSelectedMasks_iff_actualNextChart
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot)) :
    let base := P.parent r
    let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
    let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
    letI := originalRetainedOccupancyGroupoid A B P transport tp hOne Kroot E hE
    let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
    let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (n m : Nat) (owners : Fin n → Occ)
      (points : ∀ i : Fin n, Q.Point (Quotient.mk'' (anchor (owners i)).val))
      (bits : Fin n → ZMod 2) (inactivePoints : Fin m → Sigma Q.Point),
      Function.Injective (fun v : Sum (Fin n) (Fin m) =>
        match v with
        | Sum.inl i =>
            (⟨(Quotient.mk'' (anchor (owners i)).val :
              OriginalOccupancy A B P base hBase E),points i⟩ : Sigma Q.Point)
        | Sum.inr j => inactivePoints j) →
      (∀ j : Fin m, ¬Nonempty (Bridge B.source Kroot
        (originalSelectedTaggedRepresentative
          A B P transport base hBase E (inactivePoints j)).1)) →
      let old : Sum (Fin n) (Fin m) → Sigma B.Point := fun v =>
        match v with
        | Sum.inl i => ⟨(anchor (owners i)).val,
            originalSelectedReachedEclassRepresentative
              A B P transport hOne Kroot E (anchor (owners i)) (points i)⟩
        | Sum.inr j => originalSelectedTaggedRepresentative
            A B P transport base hBase E (inactivePoints j)
      let allBits : Sum (Fin n) (Fin m) → ZMod 2 := fun v =>
        match v with | Sum.inl i => bits i | Sum.inr _ => 0
      (∀ i j : Fin n, originalSelectedCompleteAtomicMask Q
        (K (owners i)) (K (owners j))
        (fun (R : owners i ⟶ owners j) => chi.value R)
        (Q.source.colour (points i) (points j)) (bits i) (bits j)) ↔
      Nonempty (OriginalActualNextQuotientChart
        A B P base hBase E Kroot phase old allBits) := by
  let base := P.parent r
  let hBase : ∀ i : A.Sorts, base = i := fun i => hOne base i
  let Occ := OriginalReachedOccupancy A B P base hBase E Kroot
  letI : Groupoid Occ := originalRetainedOccupancyGroupoid
    A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource A B P transport base hBase E
  let anchor := originalReachedOccupancyAnchor A B P base hBase E Kroot
  let K := fun o : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor o)
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  dsimp only
  intro n m owners points bits inactivePoints hSelected hInactive
  let old : Sum (Fin n) (Fin m) → Sigma B.Point := fun v =>
    match v with
    | Sum.inl i => ⟨(anchor (owners i)).val,
        originalSelectedReachedEclassRepresentative
          A B P transport hOne Kroot E (anchor (owners i)) (points i)⟩
    | Sum.inr j => originalSelectedTaggedRepresentative
        A B P transport base hBase E (inactivePoints j)
  let allBits : Sum (Fin n) (Fin m) → ZMod 2 := fun v =>
    match v with | Sum.inl i => bits i | Sum.inr _ => 0
  constructor
  · intro hMasks
    obtain ⟨next,hNames,hFine,_,hInjective,_⟩ :=
      originalRetainedMixedSelectedMasks_actualNextQuotientChart
        A B P transport tp hOne Kroot phase E hE
          n m owners points bits hMasks inactivePoints hSelected hInactive
    exact ⟨⟨next,hNames,hFine,hInjective⟩⟩
  · rintro ⟨C⟩
    have hLegal : Age.Legal B.source phase.masks old allBits := C.oldLegal
    obtain ⟨mark,hMark,hValues⟩ := Age.finite_seed_small
      B.source phase.masks phase.finite_seed_extension old allBits hLegal
    exact (originalRetainedSelectedFiniteActiveMasks_iff_oldGlobalMark
      A B P transport tp hOne Kroot phase E hE owners points bits).mpr
        ⟨mark,hMark,fun i => hValues (Sum.inl i)⟩

end
end CCO.ExactEPGeometry
