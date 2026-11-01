import CCO.ExactEPGeometry.OriginalRetainedClassBit

/-!
# B062 C81: exact retained occupancy of real successor children

For an original full RAW-exact E below the SAME chosen actual original
gate G, take any two E-supported active parents in the full reached
component. An E-class meets a chosen child of one and a chosen child
of the other exactly when their actual bits satisfy the character
equation of the whole identity bridge I_bc.

In the reverse direction C49 supplies an E-equivalent point in the
specified target parent, and the REAL marked-age rigid-mask law forces
it into the SPECIFIED target child. This is a source-to-successor
equivalence on actual nonempty named children, not on hypothetical
colour names. No quotient SAP, arbitrary mixed reverse exact descent
or automorphism-group section is assumed.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C81 exact if-and-only-if for every two actually inhabited
successor children of E-occupied reached parents. The source's
full identity bridge controls exactly their E-class occupancy;
in the reverse direction an individual original E-class is
realized in the requested child, not just somewhere in its parent. -/
theorem original_retained_children_occupancy_iff
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
    (hbc : (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).r
      b.val c.val)
    (ε : UnarySource.β (SingleStep.identification B phase) b.val)
    (η : UnarySource.β (SingleStep.identification B phase) c.val) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    (originalExactOccupancySetoid
      A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (fun i => hOne (P.parent r) i) E).r
        (⟨b.val,ε⟩ : (SingleStep.successor B phase).Sorts)
        (⟨c.val,η⟩ : (SingleStep.successor B phase).Sorts) ↔
      η.val = ε.val +
        phase.character.value
          (original_retained_identity_arrow
            A B P transport tp hOne Kroot E hE b c hbc) := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let I := SingleStep.identification B phase
  let Ibc := original_retained_identity_arrow
    A B P transport tp hOne Kroot E hE b c hbc
  let hBase : ∀ i : A.Sorts, P.parent r = i :=
    fun i => hOne (P.parent r) i
  let JE := currentOriginalExactSetoid
    A B P (P.parent r) hBase E
  let G := PrefixExactLargestLift.largest A B P transport tp r
    (current_kernel_exact_eq B Kroot)
  let JG := currentOriginalExactSetoid
    A B P (P.parent r) hBase G
  have hMask (x : B.Point b.val) (y : B.Point c.val)
      (hxy : JE.r
        (⟨b.val,x⟩ : Sigma B.Point)
        (⟨c.val,y⟩ : Sigma B.Point)) :
      UnarySource.mark I ⟨c.val,y⟩ =
        UnarySource.mark I ⟨b.val,x⟩ +
          phase.character.value Ibc := by
    have hGxy : JG.r
        (⟨b.val,x⟩ : Sigma B.Point)
        (⟨c.val,y⟩ : Sigma B.Point) := hE hxy
    have hR : Ibc.rel x y :=
      (original_retained_identity_arrow_global_iff
        A B P transport tp hOne Kroot E hE b c hbc x y).mpr hGxy
    have hLegal : phase.allows (B.source.colour x y)
        (UnarySource.mark I ⟨b.val,x⟩)
        (UnarySource.mark I ⟨c.val,y⟩) :=
      (UnarySource.global_marking I).2
        (⟨b.val,x⟩ : Sigma B.Point)
        (⟨c.val,y⟩ : Sigma B.Point)
    exact ((phase.rigid_mask_iff b c Ibc x y hR
      (UnarySource.mark I ⟨b.val,x⟩)
      (UnarySource.mark I ⟨c.val,y⟩)).mp hLegal).2.2
  constructor
  · rintro ⟨x,y,hxy⟩
    have hOld : JE.r
        (⟨b.val,x.val⟩ : Sigma B.Point)
        (⟨c.val,y.val⟩ : Sigma B.Point) := by
      change (originalExactGlobalRelation A (P.parent r) hBase E)
        (P.project ⟨b.val,x.val⟩)
        (P.project ⟨c.val,y.val⟩)
      exact hxy
    have hxMark : UnarySource.mark I ⟨b.val,x.val⟩ = ε.val :=
      congrArg Subtype.val x.property
    have hyMark : UnarySource.mark I ⟨c.val,y.val⟩ = η.val :=
      congrArg Subtype.val y.property
    calc
      η.val = UnarySource.mark I ⟨c.val,y.val⟩ := hyMark.symm
      _ = UnarySource.mark I ⟨b.val,x.val⟩ +
          phase.character.value Ibc := hMask x.val y.val hOld
      _ = ε.val + phase.character.value Ibc := by rw [hxMark]
  · intro hBit
    let x : (SingleStep.successor B phase).Point ⟨b.val,ε⟩ :=
      Classical.choice
        ((SingleStep.successor B phase).source.nonemptySort ⟨b.val,ε⟩)
    obtain ⟨y,hOld⟩ :=
      (originalExactClass_occupies_supported_type
        A B P (P.parent r) hBase E b.val c.val x.val).mp hbc
    have hxMark : UnarySource.mark I ⟨b.val,x.val⟩ = ε.val :=
      congrArg Subtype.val x.property
    have hyMark : UnarySource.mark I ⟨c.val,y⟩ = η.val := by
      calc
        UnarySource.mark I ⟨c.val,y⟩ =
            UnarySource.mark I ⟨b.val,x.val⟩ +
              phase.character.value Ibc := hMask x.val y hOld
        _ = ε.val + phase.character.value Ibc := by rw [hxMark]
        _ = η.val := hBit.symm
    have hTag : UnarySource.tag I c.val y = η :=
      Subtype.ext hyMark
    let yy : (SingleStep.successor B phase).Point ⟨c.val,η⟩ :=
      ⟨y,hTag⟩
    refine ⟨x,yy,?_⟩
    change (originalExactGlobalRelation A (P.parent r) hBase E)
      (P.project ⟨b.val,x.val⟩) (P.project ⟨c.val,y⟩)
    exact hOld

end
end CCO.ExactEPGeometry
