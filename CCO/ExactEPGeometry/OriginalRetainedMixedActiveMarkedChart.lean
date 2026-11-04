import CCO.ExactEPGeometry.OriginalRetainedSelectedFiniteActiveAgeIff
import CCO.APCharacter.Age.Realized
import CCO.APCharacter.MaskReadout

/-!
# B062 C96: finite mixed genuine marked-age chart from active quotient masks

Take an arbitrary finite set of REAL reached selected E-quotient
points with complete actual full-Arrow corrected character masks.
C91–C96 already proves that one ORIGINAL globally source-legal mark
simultaneously realizes all these active anchor E-class bits. Add an
arbitrary second finite set of REAL old points in inactive current
parents, whose only legal bit is the forced zero. If the combined old
representatives are ACTUALLY DISTINCT, the complete genuine old
fine-colour table and all the given bits form one legal finite marked
source chart. Embed that chart into the ACTUAL AP-only successor.

This is a nontrivial mixed active/inactive source-age realization
without assuming a global old marking as an EXTRA input: it is proved
from the actual active quotient C88 mask condition. The separate
remaining C89/C96 task is to derive a jointly injective old
representative chart from EVERY arbitrary locally legal COMPLETE
mixed quotient orbital diagram, and to identify its successor
quotient with the true quotient-age structure. No quotient SAP,
automorphism group section, synthetic colours, or source change.
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

/-- C96 full OLD real marked-age chart for an arbitrary finite mix:
complete selected quotient active full-arrow masks supply ONE true
old source-global marking; the inactive points carry forced zero.
The only extra chart condition is genuine distinctness of the old
representatives, necessary to preserve the complete old diagonal. -/
theorem originalRetainedMixedActiveMasks_oldMarkedChart
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
      ∀ (old : Sum (Fin n) (Fin m) → Sigma B.Point),
        (∀ i : Fin n,
          old (Sum.inl i) =
            ⟨(anchor (owners i)).val,
              originalSelectedReachedEclassRepresentative
                A B P transport hOne Kroot E
                  (anchor (owners i)) (points i)⟩) →
        (∀ j : Fin m,
          ¬Nonempty (Bridge B.source Kroot (old (Sum.inr j)).1)) →
        Function.Injective old →
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
  intro n m owners points bits hMasks old hOldAnchor hInactive hInjective
  let allBits : Sum (Fin n) (Fin m) → ZMod 2 :=
    fun v => match v with
      | Sum.inl i => bits i
      | Sum.inr _ => 0
  have hActiveIff := originalRetainedSelectedFiniteActiveMasks_iff_oldGlobalMark
    A B P transport tp hOne Kroot phase E hE
      (V := Fin n) owners points bits
  obtain ⟨mark,hGlobal,hValues⟩ := hActiveIff.mp hMasks
  have hActiveValues (i : Fin n) :
      mark (old (Sum.inl i)) = bits i := by
    rw [hOldAnchor i]
    exact hValues i
  have hValid : ∀ v : Sum (Fin n) (Fin m),
      phase.masks.validBit (old v).1 (allBits v) := by
    intro v
    cases v with
    | inl i =>
        have hv := hGlobal.1 (old (Sum.inl i))
        simpa only [allBits,hActiveValues i] using hv
    | inr j =>
        change ¬Nonempty (Bridge B.source Kroot
          (old (Sum.inr j)).1) → (0 : ZMod 2) = 0
        intro _
        rfl
  have hPair : ∀ v w : Sum (Fin n) (Fin m),
      phase.masks.allowed
        (B.source.colour (old v).2 (old w).2)
        (allBits v) (allBits w) := by
    intro v w
    cases v with
    | inl i =>
        cases w with
        | inl j =>
            have h := hGlobal.2 (old (Sum.inl i)) (old (Sum.inl j))
            simpa only [allBits,hActiveValues i,hActiveValues j] using h
        | inr j =>
            exact phase.inactive_masks_full
              (allBits (Sum.inl i)) (allBits (Sum.inr j))
              (hValid (Sum.inl i)) (hValid (Sum.inr j))
              (Or.inr (hInactive j))
              (B.source.colour (old (Sum.inl i)).2 (old (Sum.inr j)).2)
    | inr i =>
        exact phase.inactive_masks_full
          (allBits (Sum.inr i)) (allBits w)
          (hValid (Sum.inr i)) (hValid w)
          (Or.inl (hInactive i))
          (B.source.colour (old (Sum.inr i)).2 (old w).2)
  letI : Finite (Sum (Fin n) (Fin m)) := inferInstance
  exact APCharacter.Age.embed_realized B.source B.homogeneous
    (phase.completion_property B.cco)
      old allBits hInjective ⟨hValid,hPair⟩

end
end CCO.ExactEPGeometry
