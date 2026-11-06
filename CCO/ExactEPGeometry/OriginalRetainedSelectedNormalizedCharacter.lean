import CCO.ExactEPGeometry.OriginalRetainedSelectedOccupancyCharacter
import CCO.ExactEPGeometry.OriginalRetainedNormalizedArrows

/-!
# B062 C84: selected quotient character evaluates normalized full Arrows

The actual E-occupancy quotient groupoid has an entire Hom-set
equivalence between its anchor objects and the original full
Reached groupoid. Its genuine selected-source character is defined
by pulling back the ORIGINAL phase character through those
bijections. The normalized old Arrow is the literal composition
of the two actual original G-identity transports with an
ARBITRARY whole source Arrow R.

Thus the character value on its selected quotient image equals
the C79/C84 globally corrected old phase
  gamma_b + chi(R) + gamma_c.
No chosen generators, hypothetical projected gate exactness,
quotient SAP, invented group action section or reverse RAW-word
assumption enters the result.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase
open CategoryTheory

noncomputable section

/-- C84 complete selected-source character readout on EVERY genuine
old complete Arrow after actual E-occupancy anchor normalization.
This relates the TRUE source character on ALL Hom arrows, the
proved C79 object offsets, and the WHOLE selected quotient Hom
equivalence; it is not a phase merely on selected generators. -/
theorem originalRetainedSelectedNormalized_character_value
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
    let Occ := OriginalReachedOccupancy A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    letI := originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
    let ab := originalReachedOccupancyAnchor A B P
      (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
      (Quotient.mk'' b : Occ)
    let ac := originalReachedOccupancyAnchor A B P
      (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
      (Quotient.mk'' c : Occ)
    let N := originalRetainedNormalizedArrow A B P transport tp
      hOne Kroot E hE b c R
    (originalRetainedSelectedOccupancyCharacter A B P transport tp
      hOne Kroot phase E hE).value
        ((originalRetainedSelectedArrowEquiv A B P transport tp
          hOne Kroot E hE ab ac) N) =
    (originalReachedGlobalCharacter A B P transport tp
      hOne Kroot phase E hE).value R := by
  let CB := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI : Groupoid (Reached B.source Kroot) :=
    Reached.groupoid B.homogeneous CB (A := Kroot)
  let Occ := OriginalReachedOccupancy A B P (P.parent r)
    (fun i => hOne (P.parent r) i) E Kroot
  letI : Groupoid Occ :=
    originalRetainedOccupancyGroupoid A B P transport tp
      hOne Kroot E hE
  let ab := originalReachedOccupancyAnchor A B P
    (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
    (Quotient.mk'' b : Occ)
  let ac := originalReachedOccupancyAnchor A B P
    (P.parent r) (fun i => hOne (P.parent r) i) E Kroot
    (Quotient.mk'' c : Occ)
  let N := originalRetainedNormalizedArrow A B P transport tp
    hOne Kroot E hE b c R
  let e := originalRetainedSelectedArrowEquiv A B P transport tp
    hOne Kroot E hE ab ac
  calc
    (originalRetainedSelectedOccupancyCharacter A B P transport tp
      hOne Kroot phase E hE).value (e N) =
        phase.character.value N := by
          change phase.character.value (e.symm (e N)) =
            phase.character.value N
          exact congrArg (fun W => phase.character.value W)
            (e.symm_apply_apply N)
    _ = (originalReachedGlobalCharacter A B P transport tp
          hOne Kroot phase E hE).value R :=
      originalRetainedNormalizedArrow_corrected_value
        A B P transport tp hOne Kroot phase E hE b c R

end
end CCO.ExactEPGeometry
