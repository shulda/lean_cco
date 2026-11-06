import CCO.ExactEPGeometry.OriginalRetainedOccupancyGroupoid

/-!
# B062 C84: full original Arrow normalization into actual occupancy anchors

For ANY full old Reached Arrow R:b→c, take the actual E-occupancy
anchors a_b and a_c (not an arbitrary disconnected pair of objects).
C49/C78 construct whole exact G-identity bridges I_(a_b,b)
and I_(c,a_c). Their genuine source Arrow composition with R yields
an ACTUAL full exact Arrow between those selected anchor gates.

C79's bridge character cocycle and the global real E-occupancy
offsets of C84 show EXACTLY
  chi(I_(a_b,b) ; R ; I_(c,a_c)) =
      gamma_b + chi(R) + gamma_c.
This is the normalized FULL source phase, for ALL morphisms including
duplicates and identity bridges. It is not merely a character of
chosen generating arrows. The codomain quotient character and full
admissible age remain additional source obligations.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.RigidGroupoid.Phase

noncomputable section

/-- C84 genuine normalized full source Arrow: its endpoints are
the actual selected reached anchors of the original E-components,
and its relation is the whole source composite of two real
identity bridges and the given arbitrary full Arrow R. -/
noncomputable def originalRetainedNormalizedArrow
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
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
    let anchor := originalReachedOccupancyAnchorOf A B P
      (P.parent r) (fun k => hOne (P.parent r) k) E Kroot
    Arrow B.source
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) (anchor b))
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) (anchor c)) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let J := originalExactOccupancySetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E
  let anchor := originalReachedOccupancyAnchorOf A B P
    (P.parent r) (fun k => hOne (P.parent r) k) E Kroot
  let a := anchor b
  let d := anchor c
  have hb : J.r b.val a.val :=
    originalReachedOccupancyAnchorOf_supported A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot b
  have hc : J.r c.val d.val :=
    originalReachedOccupancyAnchorOf_supported A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot c
  let Iab := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE a b (J.symm hb)
  let Icd := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE c d hc
  exact (Iab.comp C R).comp C Icd

/-- The phase of the true normalized full source Arrow is EXACTLY
the global objectwise corrected original character. This holds
for every complete source Hom arrow R and every E-occupancy pair
of its endpoint sorts, including different components. -/
theorem originalRetainedNormalizedArrow_character
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
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    phase.character.value
      (originalRetainedNormalizedArrow
        A B P transport tp hOne Kroot E hE b c R) =
      originalReachedGlobalOffset A B P transport tp
        hOne Kroot phase E hE b +
      phase.character.value R +
      originalReachedGlobalOffset A B P transport tp
        hOne Kroot phase E hE c := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let J := originalExactOccupancySetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) E
  let anchor := originalReachedOccupancyAnchorOf A B P
    (P.parent r) (fun k => hOne (P.parent r) k) E Kroot
  let a := anchor b
  let d := anchor c
  let gamma : Reached B.source Kroot → ZMod 2 :=
    originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE
  have hb : J.r b.val a.val :=
    originalReachedOccupancyAnchorOf_supported A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot b
  have hc : J.r c.val d.val :=
    originalReachedOccupancyAnchorOf_supported A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E Kroot c
  let Iab := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE a b (J.symm hb)
  let Iba := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE b a hb
  let Icd := original_retained_identity_arrow A B P transport tp
    hOne Kroot E hE c d hc
  have hABeq : phase.character.value Iab =
      phase.character.value Iba := by
    have h := original_retained_gamma_add A B P transport tp
      hOne Kroot phase E hE a a b (J.refl a.val) hb
    rw [original_retained_anchor_gamma_zero
      A B P transport tp hOne Kroot phase E hE a] at h
    simpa only [zero_add] using h
  have hGB : gamma b = phase.character.value Iba := by
    change originalRetainedAnchorOffset A B P transport tp
      hOne Kroot phase E hE a b =
        phase.character.value Iba
    exact originalRetainedAnchorOffset_supported A B P transport tp
      hOne Kroot phase E hE a b hb
  have hGC : gamma c = phase.character.value Icd := by
    change originalRetainedAnchorOffset A B P transport tp
      hOne Kroot phase E hE d c =
        phase.character.value Icd
    exact originalRetainedAnchorOffset_supported A B P transport tp
      hOne Kroot phase E hE d c hc
  have hIab : phase.character.value Iab = gamma b :=
    hABeq.trans hGB.symm
  have hIcd : phase.character.value Icd = gamma c := hGC.symm
  change phase.character.value ((Iab.comp C R).comp C Icd) =
    gamma b + phase.character.value R + gamma c
  calc
    phase.character.value ((Iab.comp C R).comp C Icd) =
        phase.character.value (Iab.comp C R) +
          phase.character.value Icd :=
      phase.character.map_comp (Iab.comp C R) Icd
    _ = (phase.character.value Iab + phase.character.value R) +
          phase.character.value Icd :=
      congrArg (fun z : ZMod 2 => z + phase.character.value Icd)
        (phase.character.map_comp Iab R)
    _ = gamma b + phase.character.value R + gamma c := by
      rw [hIab,hIcd]

/-- The arbitrary full source normalized Arrow, read at its true
selected E-occupancy anchors, has exactly the C84 GLOBAL
gauge-corrected phase, with no additional character parameters. -/
theorem originalRetainedNormalizedArrow_corrected_value
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
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    phase.character.value
      (originalRetainedNormalizedArrow
        A B P transport tp hOne Kroot E hE b c R) =
      (originalReachedGlobalCharacter A B P transport tp
        hOne Kroot phase E hE).value R := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  change phase.character.value
      (originalRetainedNormalizedArrow
        A B P transport tp hOne Kroot E hE b c R) =
    originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE b +
    phase.character.value R +
    originalReachedGlobalOffset A B P transport tp
      hOne Kroot phase E hE c
  exact originalRetainedNormalizedArrow_character
    A B P transport tp hOne Kroot phase E hE b c R

end
end CCO.ExactEPGeometry
