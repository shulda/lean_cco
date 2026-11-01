import CCO.ExactEPGeometry.OriginalRetainedGlobalTrace
import CCO.APCharacter.SourcePhase

/-!
# B062 C79: composition of ALL genuine retained identity bridges

For a source-certified FULL connected phase and an ORIGINAL exact
E below the canonical maximal original exact gate G, the current
identity arrows I_pq have exactly the whole G traces.

If E-support connects p to q, the real C49 CLASSWISE occupancy
theorem supplies, for EVERY original E-class point x in p, a point
y of the SAME E-class in q. Since E <= G, this REAL y can serve as
the displayed q intermediate in I_pq ; I_qr. The other inclusion
comes directly from transitivity of the same original G.

No arbitrary mixed exact descent, quotient SAP, point-functional
bridge, unproved automorphism action section or selected-only
generating arrow is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Exact C79 bridge composition for EVERY three actual reached
types in ONE original E-occupancy component. This is equality of
whole CURRENT source Arrow values, including their actual typed
middle points in c; the original E witnesses are C49-classwise. -/
theorem original_retained_identity_arrow_comp
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (transport : ExactTraceTransport A.source B.source P)
    (tp : ExactTraceProduct A.source B.source P)
    (hOne : ∀ i j : A.Sorts, i = j)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (E : ExactEq A.source (P.parent r))
    (hE : E ≤ PrefixExactLargestLift.largest A B P transport tp r
      (current_kernel_exact_eq B Kroot))
    (b c d : Reached B.source Kroot)
    (hbc : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val c.val)
    (hcd : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r c.val d.val) :
    (original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b c hbc).comp
        (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco)
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE c d hcd) =
      original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE b d
          ((originalExactOccupancySetoid A B P (P.parent r)
            (fun k => hOne (P.parent r) k) E).trans hbc hcd) := by
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun k => hOne (P.parent r) k) E
  let hbd : J.r b.val d.val := J.trans hbc hcd
  let G := PrefixExactLargestLift.largest A B P transport tp r
    (current_kernel_exact_eq B Kroot)
  let GE := currentOriginalExactSetoid A B P (P.parent r)
    (fun k => hOne (P.parent r) k) G
  apply Arrow.ext
  funext x z
  apply propext
  change (∃ y : B.Point c.val,
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE b c hbc).rel x y ∧
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE c d hcd).rel y z) ↔
      (original_retained_identity_arrow
        A B P transport tp hOne Kroot E hE b d hbd).rel x z
  constructor
  · rintro ⟨y,hxy,hyz⟩
    apply (original_retained_identity_arrow_global_iff
      A B P transport tp hOne Kroot E hE b d hbd x z).mpr
    exact GE.trans
      ((original_retained_identity_arrow_global_iff
        A B P transport tp hOne Kroot E hE b c hbc x y).mp hxy)
      ((original_retained_identity_arrow_global_iff
        A B P transport tp hOne Kroot E hE c d hcd y z).mp hyz)
  · intro hxz
    have hGxz : GE.r
        (⟨b.val,x⟩ : Sigma B.Point)
        (⟨d.val,z⟩ : Sigma B.Point) :=
      (original_retained_identity_arrow_global_iff
        A B P transport tp hOne Kroot E hE b d hbd x z).mp hxz
    obtain ⟨y,hExy⟩ :=
      (originalExactClass_occupies_supported_type
        A B P (P.parent r)
          (fun k => hOne (P.parent r) k) E b.val c.val x).mp hbc
    have hGxy : GE.r
        (⟨b.val,x⟩ : Sigma B.Point)
        (⟨c.val,y⟩ : Sigma B.Point) := hE hExy
    refine ⟨y,?_,?_⟩
    · exact (original_retained_identity_arrow_global_iff
        A B P transport tp hOne Kroot E hE b c hbc x y).mpr hGxy
    · apply (original_retained_identity_arrow_global_iff
        A B P transport tp hOne Kroot E hE c d hcd y z).mpr
      exact GE.trans (GE.symm hGxy) hGxz

/-- C79's actual character 1-cocycle, for all real whole retained
identity arrows. This uses the TRUE full-reached source Phase
character rather than a separately chosen abstract character on a
smaller groupoid. -/
theorem original_retained_identity_character_cocycle
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
    (b c d : Reached B.source Kroot)
    (hbc : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r b.val c.val)
    (hcd : (originalExactOccupancySetoid A B P (P.parent r)
      (fun k => hOne (P.parent r) k) E).r c.val d.val) :
    phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b c hbc) +
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE c d hcd) =
      phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b d
            ((originalExactOccupancySetoid A B P (P.parent r)
              (fun k => hOne (P.parent r) k) E).trans hbc hcd)) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let Ibc := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b c hbc
  let Icd := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE c d hcd
  let hbd := (originalExactOccupancySetoid A B P
    (P.parent r) (fun k => hOne (P.parent r) k) E).trans hbc hcd
  let Ibd := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b d hbd
  have hComp : Ibc.comp C Icd = Ibd :=
    original_retained_identity_arrow_comp
      A B P transport tp hOne Kroot E hE b c d hbc hcd
  calc
    phase.character.value Ibc + phase.character.value Icd =
        phase.character.value (Ibc.comp C Icd) :=
      (phase.character.map_comp Ibc Icd).symm
    _ = phase.character.value Ibd := congrArg
      (fun R => phase.character.value R) hComp

end
end CCO.ExactEPGeometry
