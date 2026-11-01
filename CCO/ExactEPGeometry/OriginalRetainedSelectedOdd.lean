import CCO.ExactEPGeometry.OriginalRetainedSelectedNormalizedCharacter
import CCO.APCharacter.SourcePhase
import Mathlib.Tactic.Abel

/-!
# B062 C85: the ACTUAL selected quotient still detects the chosen odd arrow

The true original SourcePhase supplies ONE distinguished nonidentity
involution in its full Reached groupoid and its genuine full character.
Normalize the entire old odd Arrow at the ACTUAL reached anchor of its
original E-occupancy component, and apply the already proved complete
C83 selected quotient Arrow equivalence.

The actual selected occupancy-groupoid character evaluates this Arrow
as one, since the real endpoint corrections occur twice at the same
source object and therefore cancel in ZMod 2. Hence the selected odd
Arrow is not its FULL projected gate identity. The original odd source
is retained; no independent quotient character, SAP, action section
or fictitious diversity diagonal has been postulated.

Further maximality, phase mask correspondence and finite-age converse
remain separate C85-C105 source obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- The REAL selected odd Arrow is the normalized image of the true
SourcePhase odd FULL exact relation, based at the genuine occupancy
anchor containing the source's actual root. -/
noncomputable def originalRetainedSelectedOdd
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
    letI := originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
    let o : Reached B.source Kroot := Reached.root Kroot
    let q : Occ := Quotient.mk'' o
    q ⟶ q := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let o : Reached B.source Kroot := Reached.root Kroot
  let q : Occ := Quotient.mk'' o
  let a := originalReachedOccupancyAnchor A B P
    (P.parent r) (fun i => hOne (P.parent r) i) E Kroot q
  exact (originalRetainedSelectedArrowEquiv A B P transport tp
    hOne Kroot E hE a a)
    (originalRetainedNormalizedArrow A B P transport tp
      hOne Kroot E hE o o phase.odd)

/-- C85, the original distinguished full odd gate bridge survives
selection with character ONE. This uses the actual already proved
C84 complete source-to-selected character readout; no separate
quotient detection assumption is introduced. -/
theorem originalRetainedSelectedOdd_detected
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
    letI := originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
    (originalRetainedSelectedOccupancyCharacter A B P transport tp
      hOne Kroot phase E hE).value
      (originalRetainedSelectedOdd A B P transport tp
        hOne Kroot phase E hE) = (1 : ZMod 2) := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous CB (A := Kroot)
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let o : Reached B.source Kroot := Reached.root Kroot
  let gamma : Reached B.source Kroot → ZMod 2 :=
    originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE
  have hRead := originalRetainedSelectedNormalized_character_value
    A B P transport tp hOne Kroot phase E hE o o phase.odd
  have hCorrected :
      (originalReachedGlobalCharacter A B P transport tp
        hOne Kroot phase E hE).value phase.odd = (1 : ZMod 2) := by
    change gamma o + phase.character.value phase.odd + gamma o = 1
    rw [phase.detects]
    have hDouble : ∀ z : ZMod 2, z + z = 0 := by decide
    calc
      gamma o + 1 + gamma o = (gamma o + gamma o) + 1 := by abel
      _ = 1 := by rw [hDouble]; exact zero_add 1
  exact hRead.trans hCorrected

/-- Character detection makes the actual selected full odd Arrow
nonidentity. The selected groupoid identity is the ENTIRE projected
K/E gate relation and must never be confused with logical equality. -/
theorem originalRetainedSelectedOdd_nonidentity
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
    letI := originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
    let q : Occ := Quotient.mk'' (Reached.root Kroot)
    originalRetainedSelectedOdd A B P transport tp
      hOne Kroot phase E hE ≠ 𝟙 q := by
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let q : Occ := Quotient.mk'' (Reached.root Kroot)
  let chi := originalRetainedSelectedOccupancyCharacter
    A B P transport tp hOne Kroot phase E hE
  have hOneVal : chi.value
      (originalRetainedSelectedOdd A B P transport tp
        hOne Kroot phase E hE) = 1 :=
    originalRetainedSelectedOdd_detected
      A B P transport tp hOne Kroot phase E hE
  change originalRetainedSelectedOdd A B P transport tp
    hOne Kroot phase E hE ≠ (𝟙 q)
  intro h
  have hEq := congrArg (fun R : q ⟶ q => chi.value R) h
  have hZero : chi.value (𝟙 q) = 0 := chi.map_id q
  have hBad : (1 : ZMod 2) = 0 :=
    hOneVal.symm.trans (hEq.trans hZero)
  exact (by decide : (1 : ZMod 2) ≠ 0) hBad

end
end CCO.ExactEPGeometry
