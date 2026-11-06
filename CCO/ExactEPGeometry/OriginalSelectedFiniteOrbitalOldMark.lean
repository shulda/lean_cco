import CCO.ExactEPGeometry.OriginalSelectedFiniteAnchorBits
import CCO.ExactEPGeometry.OriginalRetainedSelectedOrbitalSeeds

/-!
# B062 C91–C95: finite actual quotient masks produce genuine old marked witnesses

Given ANY finite family of ACTUALLY REALIZED points of the genuine
E-occupancy selected quotient prefix and locally legal full selected
Arrow-character atomic masks, the actual C91–C93 free-action theorem
produces one full selected groupoid marking satisfying every bit.
The completed C93/C94 source transport then gives ONE genuinely
global old SourcePhase marking, and the exact anchor E-class
representatives attain precisely the prescribed bits.

This is simultaneous in all finite vertices, including presentations
of duplicate K/E gate points: their selected bits are compatible
because the whole gate identity has character zero. The underlying
fine old orbitals are taken from the real old prefix source, never
guessed or selected independently.

This does NOT realize an arbitrary unmarked locally admissible
quotient-prefix diagram (C89 requires the inductive full-age
hypothesis), and it does NOT assert the full quotient marked-age
coincidence or the complete safe tower. There is no quotient SAP,
group action section or new axiom.
-/

universe u v w t z

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

theorem originalRetainedSelectedFiniteOrbitalOldMark
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
    ∀ {V : Type z} [Finite V]
      (owners : V → Occ)
      (point : ∀ v : V,
        Q.Point (Quotient.mk'' (anchor (owners v)).val))
      (bits : V → ZMod 2),
      (∀ i j : V,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (point i) (point j))
          (bits i) (bits j)) →
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ v : V,
            oldMark ⟨(anchor (owners v)).val,
              originalSelectedReachedEclassRepresentative
                A B P transport hOne Kroot E
                (anchor (owners v)) (point v)⟩ = bits v := by
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
  change ∀ {V : Type z} [Finite V]
      (owners : V → Occ)
      (point : ∀ v : V,
        Q.Point (Quotient.mk'' (anchor (owners v)).val))
      (bits : V → ZMod 2),
      (∀ i j : V,
        originalSelectedCompleteAtomicMask Q
          (K (owners i)) (K (owners j))
          (fun (R : owners i ⟶ owners j) => chi.value R)
          (Q.source.colour (point i) (point j))
          (bits i) (bits j)) →
      ∃ oldMark : Sigma B.Point → ZMod 2,
        phase.masks.GlobalMarking oldMark ∧
          ∀ v : V,
            oldMark ⟨(anchor (owners v)).val,
              originalSelectedReachedEclassRepresentative
                A B P transport hOne Kroot E
                (anchor (owners v)) (point v)⟩ = bits v
  intro V _ owners point bits hAllowed
  obtain ⟨selectedMark,hSelected,hBits⟩ :=
    originalRetainedSelectedFiniteOrbitalSeedExtension
      A B P transport tp hOne Kroot phase E hE owners point bits hAllowed
  obtain ⟨oldMark,hGlobal,hExact⟩ :=
    originalSelectedFullMark_exactAnchorBits
      A B P transport tp hOne Kroot phase E hE selectedMark hSelected
  refine ⟨oldMark,hGlobal,?_⟩
  intro v
  exact (hExact (owners v) (point v)).trans (hBits v)

end
end CCO.ExactEPGeometry
