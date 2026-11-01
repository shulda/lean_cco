import CCO.ExactEPGeometry.OriginalRetainedGamma
import CCO.APCharacter.MaskReadout
import CCO.APCharacter.SourceAge.SingleStep
import Mathlib.Tactic.Abel

/-!
# B062 C80: corrected actual bits of individual original E-classes

Fix the ACTUAL current homogeneous prefix and SAME real SourcePhase
with the full connected rigid groupoid. E is a genuine ORIGINAL full
RAW-exact equivalence below its selected greatest original gate G.

For any reached anchor a and two reached types b,c belonging to the
same ORIGINAL E-occupancy component, two REAL points x,y in ONE
original E-class have equal corrected phase values:

 mark(x) + chi(I_ba) = mark(y) + chi(I_ca).

The full source C49 pair-occupancy witnesses, C78 actual I_bc Arrow,
the actual marked-age GLOBAL legality and SOURCE rigid_mask_iff
discharge the entire statement. The unique G trace Arrow acts on
actual gate classes, never as a function on individual old points.
No quotient action section or quotient SAP is assumed.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Source C80, at EVERY original E-related real pair in the same
retained occupancy component: after the coherent anchor correction,
their actual canonical next child bits agree. All support, transport,
character and legality data belong to the SAME source-certified step. -/
theorem original_retained_class_corrected_phase_invariant
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
    (a b c : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val a.val)
    (hca : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r c.val a.val)
    (x : B.Point b.val) (y : B.Point c.val)
    (hExy : (currentOriginalExactSetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r
      (⟨b.val,x⟩ : Sigma B.Point)
      (⟨c.val,y⟩ : Sigma B.Point)) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    let I := SingleStep.identification B phase
    UnarySource.mark I ⟨b.val,x⟩ +
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b a hba) =
    UnarySource.mark I ⟨c.val,y⟩ +
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE c a hca) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let I := SingleStep.identification B phase
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  let hbc : J.r b.val c.val := J.trans hba (J.symm hca)
  let Ibc := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b c hbc
  let Iba := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b a hba
  let Ica := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE c a hca
  let G := PrefixExactLargestLift.largest A B P transport tp r
    (current_kernel_exact_eq B Kroot)
  let JG := currentOriginalExactSetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) G
  have hGxy : JG.r
      (⟨b.val,x⟩ : Sigma B.Point)
      (⟨c.val,y⟩ : Sigma B.Point) := hE hExy
  have hR : Ibc.rel x y :=
    (original_retained_identity_arrow_global_iff
      A B P transport tp hOne Kroot E hE b c hbc x y).mpr hGxy
  have hLegal : phase.allows (B.source.colour x y)
      (UnarySource.mark I ⟨b.val,x⟩)
      (UnarySource.mark I ⟨c.val,y⟩) :=
    (UnarySource.global_marking I).2
      (⟨b.val,x⟩ : Sigma B.Point)
      (⟨c.val,y⟩ : Sigma B.Point)
  have hMark : UnarySource.mark I ⟨c.val,y⟩ =
      UnarySource.mark I ⟨b.val,x⟩ +
        phase.character.value Ibc :=
    (phase.rigid_mask_iff b c Ibc x y hR
      (UnarySource.mark I ⟨b.val,x⟩)
      (UnarySource.mark I ⟨c.val,y⟩)).mp hLegal |>.2.2
  have hGamma : phase.character.value Ibc =
      phase.character.value Iba + phase.character.value Ica :=
    original_retained_gamma_add
      A B P transport tp hOne Kroot phase E hE a b c hba hca
  have hDouble : ∀ z : ZMod 2, z + z = 0 := by decide
  calc
    UnarySource.mark I ⟨b.val,x⟩ + phase.character.value Iba =
        UnarySource.mark I ⟨b.val,x⟩ +
          (phase.character.value Iba +
            (phase.character.value Ica + phase.character.value Ica)) := by
      rw [hDouble]
      simp
    _ = (UnarySource.mark I ⟨b.val,x⟩ +
          (phase.character.value Iba + phase.character.value Ica)) +
            phase.character.value Ica := by abel
    _ = (UnarySource.mark I ⟨b.val,x⟩ +
          phase.character.value Ibc) + phase.character.value Ica := by
      rw [hGamma]
    _ = UnarySource.mark I ⟨c.val,y⟩ +
          phase.character.value Ica := by
      rw [hMark]

end
end CCO.ExactEPGeometry
