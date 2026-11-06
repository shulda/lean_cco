import CCO.ExactEPGeometry.OriginalDiscardedGateBit
import CCO.ExactEPGeometry.OriginalExactOccupancy

/-!
# B062 C76: an ACTUAL discarded split does not separate original E-classes

Fix an original one-sort FULL RAW-exact E NOT below the canonical
original maximal gate of one REAL AP-only SourcePhase. At EVERY reached
active current parent, the source C73-C75 theorem provides for EACH
real old E-class member x an E-equivalent y with opposite ACTUAL bit.

The successor is the literal Rank.Child / Rank.Point source of this
SAME SourcePhase. Here we prove the opposite y lies in an ACTUAL
occupied successor child with the SAME parent but DIFFERENT bit,
and remains in the SAME GLOBAL ORIGINAL E-class on the genuine
composite old-to-successor reduct. Consequently its successor child
sort lies in precisely the SAME real E-occupancy class.

This is classwise nonrefinement of the new unary partition inside each
active old parent. The full discarded-step identification across
DIFFERENT active parents, preservation of all old occupancy classes
and the later quotient transition require an additional C76 consumer.

No SAP, automorphism group section, fake quotient action or
unproved existence of a marked child.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- For EVERY real point of an ACTUAL active successor child, there
is a DIFFERENT actual child of the SAME current parent, and a point
of that child in the SAME global original E-class. The new child's
actual phase bit differs by 1. No arbitrary nominal child is used. -/
theorem original_discarded_each_class_reaches_opposite_child
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
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot)
    (c : UnarySource.β (SingleStep.identification B phase) b.val)
    (x : (SingleStep.successor B phase).Point ⟨b.val,c⟩) :
    ∃ d : UnarySource.β (SingleStep.identification B phase) b.val,
      d.val = c.val + (1 : Bit) ∧ d ≠ c ∧
      ∃ y : (SingleStep.successor B phase).Point ⟨b.val,d⟩,
        (currentOriginalExactSetoid
          A (SingleStep.successor B phase)
          (P.compose (SingleStep.projection B phase))
          (P.parent r) (fun i => hOne (P.parent r) i) E).r
          (⟨⟨b.val,c⟩,x⟩ : Sigma (SingleStep.successor B phase).Point)
          (⟨⟨b.val,d⟩,y⟩ : Sigma (SingleStep.successor B phase).Point) := by
  let I := SingleStep.identification B phase
  obtain ⟨y,hEy,hOpp⟩ :=
    original_discarded_each_active_class_opposite_child
      A B P transport tp hOne Kroot phase E hNot b x.val
  let d : UnarySource.β I b.val := UnarySource.tag I b.val y
  let yy : (SingleStep.successor B phase).Point ⟨b.val,d⟩ :=
    ⟨y,rfl⟩
  have hxMark : UnarySource.mark I ⟨b.val,x.val⟩ = c.val :=
    congrArg Subtype.val x.property
  have hBit : d.val = c.val + (1 : Bit) := by
    change UnarySource.mark I ⟨b.val,y⟩ = _
    exact hOpp.trans (congrArg (fun v : Bit => v + (1 : Bit)) hxMark)
  have hDifferent : d ≠ c := by
    intro hdc
    have hOneZero : (1 : Bit) = 0 := by
      have hEq : c.val + (1 : Bit) = c.val + 0 := by
        simpa only [add_zero] using
          (hBit.symm.trans (congrArg Subtype.val hdc))
      exact add_left_cancel hEq
    exact (by decide : (1 : Bit) ≠ 0) hOneZero
  refine ⟨d,hBit,hDifferent,yy,?_⟩
  have hLocal :
      (oldExactEqCast A.source
        (hOne (P.parent r) (P.parent b.val)).symm E)
          (P.point b.val x.val) (P.point b.val y) :=
    (PrefixExactRestriction.rho_iff A B P transport b.val
      (oldExactEqCast A.source
        (hOne (P.parent r) (P.parent b.val)).symm E)
      x.val y).mp hEy
  have hOriginal : E
      ((hOne (P.parent r) (P.parent b.val)).symm ▸ P.point b.val x.val)
      ((hOne (P.parent r) (P.parent b.val)).symm ▸ P.point b.val y) :=
    (oldExactEqCast_iff A.source
      (hOne (P.parent r) (P.parent b.val)).symm E
      (P.point b.val x.val) (P.point b.val y)).mp hLocal
  change E
    ((hOne (P.parent r) (P.parent b.val)).symm ▸ P.point b.val x.val)
    ((hOne (P.parent r) (P.parent b.val)).symm ▸ P.point b.val y)
  exact hOriginal

/-- Consequently the literal two opposite new successor NAMES lie
in the SAME original-E occupancy class. This is proved from REAL
successor pair witnesses, not a nominal colour/bit assertion. -/
theorem original_discarded_active_opposite_child_same_occupancy
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
    (hNot : ¬ E ≤ PrefixExactLargestLift.largest
      A B P transport tp r (current_kernel_exact_eq B Kroot))
    (b : Reached B.source Kroot)
    (c : UnarySource.β (SingleStep.identification B phase) b.val)
    (x : (SingleStep.successor B phase).Point ⟨b.val,c⟩) :
    ∃ d : UnarySource.β (SingleStep.identification B phase) b.val,
      d ≠ c ∧
      (originalExactOccupancySetoid
        A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase))
        (P.parent r) (fun i => hOne (P.parent r) i) E).r
          ⟨b.val,c⟩ ⟨b.val,d⟩ := by
  obtain ⟨d,_,hDifferent,y,hRel⟩ :=
    original_discarded_each_class_reaches_opposite_child
      A B P transport tp hOne Kroot phase E hNot b c x
  refine ⟨d,hDifferent,?_⟩
  change ∃ x' : (SingleStep.successor B phase).Point ⟨b.val,c⟩,
    ∃ y' : (SingleStep.successor B phase).Point ⟨b.val,d⟩,
      (currentOriginalExactSetoid
        A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase))
        (P.parent r) (fun i => hOne (P.parent r) i) E).r
        (⟨⟨b.val,c⟩,x'⟩ : Sigma (SingleStep.successor B phase).Point)
        (⟨⟨b.val,d⟩,y'⟩ : Sigma (SingleStep.successor B phase).Point)
  exact ⟨x,y,hRel⟩

end
end CCO.ExactEPGeometry
