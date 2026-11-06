import CCO.ExactEPGeometry.OriginalRetainedIdentityComposition
import Mathlib.Tactic.Abel

/-!
# B062 C79: normalized exact identity transports and objectwise phases

The genuinely constructed G-identity bridges form an honest subgroupoid
on each retained original E-occupancy component. Its diagonal
bridge is the whole current EXACT gate (not logical equality). The
actual full SourcePhase character is additive on these bridges.

Choosing any reached anchor parent a in this REAL component gives
gamma_b = chi(I_ba) and gamma_a=0, with
  chi(I_bc) = gamma_b + gamma_c
for all b,c of the same component (values in ZMod 2).

The anchor can subsequently be chosen as the ACTUAL selected
occupancy representative; no independent quotient section or
new source homogeneity/SAP has been assumed.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C79: the whole original gate trace at a single genuine reached
parent IS its actual full exact gate identity. The old source
one-sort equality is used only through a reflexive dependent cast. -/
theorem original_retained_identity_arrow_self
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
    original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b b
        ((originalExactOccupancySetoid A B P (P.parent r)
          (fun k => hOne (P.parent r) k) E).refl b.val) =
      Arrow.id (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  let Gb := PrefixExactLargestLift.largest A B P transport tp b.val
    (current_kernel_exact_eq B Kb)
  have hSpec : PrefixExactRestriction.rho A B P transport b.val Gb =
      current_kernel_exact_eq B Kb :=
    (PrefixExactLargestLift.largest_spec
      A B P transport tp b.val (current_kernel_exact_eq B Kb)).1
  have hReflCast (y : B.Point b.val) :
      ((hOne (P.parent b.val) (P.parent b.val)).symm ▸
        P.point b.val y) = P.point b.val y := by
    have hrefl : hOne (P.parent b.val) (P.parent b.val) =
        (rfl : P.parent b.val = P.parent b.val) := Subsingleton.elim _ _
    rw [hrefl]
  apply Arrow.ext
  funext x y
  apply propext
  calc
    (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE b b
          ((originalExactOccupancySetoid A B P (P.parent r)
            (fun k => hOne (P.parent r) k) E).refl b.val)).rel x y ↔
        Gb (P.point b.val x)
          ((hOne (P.parent b.val) (P.parent b.val)).symm ▸
            P.point b.val y) :=
      original_retained_identity_arrow_iff
        A B P transport tp hOne Kroot E hE b b
          ((originalExactOccupancySetoid A B P (P.parent r)
            (fun k => hOne (P.parent r) k) E).refl b.val) x y
    _ ↔ Gb (P.point b.val x) (P.point b.val y) := by
      rw [hReflCast y]
    _ ↔ (PrefixExactRestriction.rho A B P transport b.val Gb) x y :=
      (PrefixExactRestriction.rho_iff A B P transport b.val Gb x y).symm
    _ ↔ Kb.rel x y := by
      rw [hSpec]
      exact Iff.rfl

/-- At the selected active anchor, gamma=chi(I_aa)=0 since its
whole exact gate bridge is the genuine identity of the FULL
Reached groupoid. -/
theorem original_retained_anchor_gamma_zero
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
      (current_kernel_exact_eq B Kroot))
    (a : Reached B.source Kroot) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    phase.character.value
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE a a
          ((originalExactOccupancySetoid A B P (P.parent r)
            (fun k => hOne (P.parent r) k) E).refl a.val)) = 0 := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  rw [original_retained_identity_arrow_self
    A B P transport tp hOne Kroot E hE a]
  exact phase.character.map_id a

/-- C79 normalized phase: any chosen ACTUAL reached anchor a gives
the precise old identity-bridge 1-coboundary on its entire
retained E-component. This is the genuine source character, not an
arbitrarily chosen function on the current sort set. -/
theorem original_retained_gamma_add
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
      (current_kernel_exact_eq B Kroot))
    (a b c : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val a.val)
    (hca : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r c.val a.val) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    phase.character.value
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE b c
          ((originalExactOccupancySetoid A B P (P.parent r)
            (fun k => hOne (P.parent r) k) E).trans hba
              ((originalExactOccupancySetoid A B P (P.parent r)
                (fun k => hOne (P.parent r) k) E).symm hca))) =
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b a hba) +
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE c a hca) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  let hbc : J.r b.val c.val := J.trans hba (J.symm hca)
  let Ibc := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b c hbc
  let Ica := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE c a hca
  let Iba := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b a hba
  have hCocycle :
      phase.character.value Ibc + phase.character.value Ica =
        phase.character.value Iba :=
    original_retained_identity_character_cocycle
      A B P transport tp hOne Kroot phase E hE b c a hbc hca
  have hDouble : ∀ z : ZMod 2, z + z = 0 := by decide
  calc
    phase.character.value Ibc =
        phase.character.value Ibc + 0 := (add_zero _).symm
    _ = phase.character.value Ibc +
          (phase.character.value Ica + phase.character.value Ica) := by
      rw [hDouble]
    _ = (phase.character.value Ibc + phase.character.value Ica) +
        phase.character.value Ica := by abel
    _ = phase.character.value Iba + phase.character.value Ica := by
      rw [hCocycle]

end
end CCO.ExactEPGeometry
