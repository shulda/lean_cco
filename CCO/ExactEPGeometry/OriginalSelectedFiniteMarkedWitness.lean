import CCO.ExactEPGeometry.OriginalSelectedFiniteOrbitalOldMark
import CCO.ExactEPGeometry.OriginalSelectedFiniteReachedInjectivity
import CCO.APCharacter.Age.Realized
import CCO.APCharacter.MarkedSource

/-!
# B062 C91–C95: ACTUAL finite selected quotient mark realized in the genuine old marked age

Take any finite INJECTIVE list of ACTUALLY REALIZED selected E-quotient
prefix vertices at the reached E-occupancy anchors. Assume their real
selected atomic colours obey the genuine complete C84 full Arrow masks.
The C91–C93 full free-action extension constructs one global selected
mark, its real C93/C94 pullback constructs ONE old source global
mark attaining ALL prescribed bits, and the proved literal E-class
representatives are pairwise distinct.

Consequently the complete original fine pair-orbital table and EVERY
unary owner/phase name of those representatives form an ACTUAL finite
old marked-age object, which embeds with all names preserved into the
genuine AP-only homogeneous marked successor.

This makes no claim that every arbitrary locally allowed unmarked
quotient-prefix diagram already occurs in the actual source (C89
inductive full-age obligation), and does not assert the converse
entire quotient marked-age identification C96. The original whole
K/E gate identities, source AP-only marking and inactive bit rule
are respected; no quotient SAP or invented group section is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory
open OwnerTransversal.CountableColour

noncomputable section

theorem originalRetainedSelectedFiniteOrbitalOldMarkedWitness
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
      A B P transport (P.parent r) (fun i => hOne (P.parent r) i) E
    let anchor := originalReachedOccupancyAnchor
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
    let K := fun o : Occ => originalRetainedSelectedKernel
      A B P transport tp hOne Kroot E hE (anchor o)
    let chi := originalRetainedSelectedOccupancyCharacter
      A B P transport tp hOne Kroot phase E hE
    ∀ (n : Nat) (owners : Fin n → Occ)
      (point : ∀ i : Fin n,
        Q.Point (Quotient.mk'' (anchor (owners i)).val))
      (bits : Fin n → ZMod 2),
      (∀ i j : Fin n,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (point i) (point j))
          (bits i) (bits j)) →
      Function.Injective (fun i : Fin n =>
        (⟨(Quotient.mk'' (anchor (owners i)).val :
            OriginalOccupancy A B P (P.parent r)
              (fun k => hOne (P.parent r) k) E),point i⟩ :
        Sigma Q.Point)) →
      let old : Fin n → Sigma B.Point := fun i =>
        ⟨(anchor (owners i)).val,
          originalSelectedReachedEclassRepresentative
            A B P transport hOne Kroot E
              (anchor (owners i)) (point i)⟩
      ∃ f : Fin n ↪ phase.MarkedLimit B.cco,
        (∀ i, (phase.markedCoding B.cco).table.owner (f i) =
          APCharacter.Age.ownerEquiv B.source ((old i).1,bits i)) ∧
        ∀ i j, (phase.markedCoding B.cco).table.colour (f i) (f j) =
          APCharacter.Age.colourEquiv B.source
            (taggedColour B.source (old i) (old j)) := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid
      A B P transport tp hOne Kroot E hE
  let Q := originalExactSelectedQuotientCurrentSource
    A B P transport (P.parent r) (fun i => hOne (P.parent r) i) E
  let anchor := originalReachedOccupancyAnchor
    A B P (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
  let K := fun o : Occ => originalRetainedSelectedKernel
    A B P transport tp hOne Kroot E hE (anchor o)
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  change ∀ (n : Nat) (owners : Fin n → Occ)
      (point : ∀ i : Fin n,
        Q.Point (Quotient.mk'' (anchor (owners i)).val))
      (bits : Fin n → ZMod 2),
      (∀ i j : Fin n,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (point i) (point j))
          (bits i) (bits j)) →
      Function.Injective (fun i : Fin n =>
        (⟨(Quotient.mk'' (anchor (owners i)).val :
            OriginalOccupancy A B P (P.parent r)
              (fun k => hOne (P.parent r) k) E),point i⟩ :
        Sigma Q.Point)) →
      let old : Fin n → Sigma B.Point := fun i =>
        ⟨(anchor (owners i)).val,
          originalSelectedReachedEclassRepresentative
            A B P transport hOne Kroot E
              (anchor (owners i)) (point i)⟩
      ∃ f : Fin n ↪ phase.MarkedLimit B.cco,
        (∀ i, (phase.markedCoding B.cco).table.owner (f i) =
          APCharacter.Age.ownerEquiv B.source ((old i).1,bits i)) ∧
        ∀ i j, (phase.markedCoding B.cco).table.colour (f i) (f j) =
          APCharacter.Age.colourEquiv B.source
            (taggedColour B.source (old i) (old j))
  intro n owners point bits hAllowed hDistinct
  let old : Fin n → Sigma B.Point := fun i =>
    ⟨(anchor (owners i)).val,
      originalSelectedReachedEclassRepresentative
        A B P transport hOne Kroot E
          (anchor (owners i)) (point i)⟩
  have hOldInjective : Function.Injective old :=
    originalSelectedFiniteReachedRepresentative_injective
      A B P transport hOne Kroot E owners point hDistinct
  obtain ⟨oldMark,hGlobal,hExact⟩ :=
    originalRetainedSelectedFiniteOrbitalOldMark
      A B P transport tp hOne Kroot phase E hE
        owners point bits hAllowed
  have hLegal : APCharacter.Age.Legal B.source phase.masks old bits := by
    constructor
    · intro i
      have h := hGlobal.1 (old i)
      have hi : oldMark (old i) = bits i := hExact i
      rw [hi] at h
      exact h
    · intro i j
      have h := hGlobal.2 (old i) (old j)
      have hi : oldMark (old i) = bits i := hExact i
      have hj : oldMark (old j) = bits j := hExact j
      rw [hi,hj] at h
      exact h
  exact APCharacter.Age.embed_realized
    B.source B.homogeneous (phase.completion_property B.cco)
      old bits hOldInjective hLegal

end
end CCO.ExactEPGeometry
