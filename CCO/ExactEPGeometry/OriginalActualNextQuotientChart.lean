import CCO.ExactEPGeometry.OriginalRetainedActualNextSaturatedColour
import CCO.APCharacter.Age.Reasonableness

/-!
# B062 C96: a concrete actual quotient chart and its full NEW palette

This is finite witness data in the true successor: actual point images,
their child names, every fine old colour and distinct global original-E
classes. It is not a provider for an unconstructed quotient source.

Every such witness gives local old marked legality in the reverse
direction. At a retained step its WHOLE new saturated palette is read
from the old saturated palette together with literal child occupancies.
-/

universe u v w t z
namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry

noncomputable section

/-- Concrete actual-successor witness, with no collapse of true E-classes. -/
structure OriginalActualNextQuotientChart
    (A B : CurrentSource.{u,v,w,t})
    (P : UnaryReduct A.source B.source)
    (base : A.Sorts) (hBase : ∀ i : A.Sorts, base = i)
    (E : ExactEq A.source base)
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot)
    {V : Type z} (old : V → Sigma B.Point) (bits : V → ZMod 2) where
  point : V ↪ Sigma (SingleStep.successor B phase).Point
  names : ∀ v, UnarySource.childLabel (SingleStep.identification B phase)
    (point v).1 = ((old v).1,bits v)
  fine : ∀ v w, taggedColour B.source
    ((SingleStep.projection B phase).project (point v))
    ((SingleStep.projection B phase).project (point w)) =
      taggedColour B.source (old v) (old w)
  quotient_injective : Function.Injective (fun v =>
    (Quotient.mk'' (point v) : Quotient
      (currentOriginalExactSetoid A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase)) base hBase E)))

/-- Every actual next chart obeys ALL old local marking rules. This is
the reverse marked-age implication, read from the actual constructed
marking rather than supplied as an extra hypothesis about the output. -/
theorem OriginalActualNextQuotientChart.oldLegal
    {A B : CurrentSource.{u,v,w,t}}
    {P : UnaryReduct A.source B.source}
    {base : A.Sorts} {hBase : ∀ i : A.Sorts, base = i}
    {E : ExactEq A.source base}
    {r : B.Sorts} {Kroot : Kernel B.source r}
    {phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO B.source B.homogeneous B.cco) Kroot}
    {V : Type} {old : V → Sigma B.Point} {bits : V → ZMod 2}
    (C : OriginalActualNextQuotientChart A B P base hBase E Kroot phase old bits) :
    Age.Legal B.source phase.masks old bits := by
  let I := SingleStep.identification B phase
  let R := SingleStep.projection B phase
  let mark := UnarySource.mark I
  have hMark := UnarySource.global_marking I
  have hBits (v : V) : mark (R.project (C.point v)) = bits v := by
    have hp : mark (R.project (C.point v)) = (C.point v).1.2.val :=
      congrArg Subtype.val (C.point v).2.property
    exact hp.trans (congrArg Prod.snd (C.names v))
  have hLegal : Age.Legal B.source phase.masks
      (fun v => R.project (C.point v)) bits := by
    constructor
    · intro v
      have h := hMark.1 (R.project (C.point v))
      change phase.masks.validBit (R.project (C.point v)).1
        (mark (R.project (C.point v))) at h
      rw [hBits v] at h
      exact h
    · intro v w
      have h := hMark.2 (R.project (C.point v)) (R.project (C.point w))
      change phase.masks.allowed
        (B.source.colour (R.project (C.point v)).2 (R.project (C.point w)).2)
        (mark (R.project (C.point v))) (mark (R.project (C.point w))) at h
      rw [hBits v,hBits w] at h
      exact h
  exact Age.legal_of_names B.source phase.masks hLegal
    (fun v w => (C.fine v w).symm)

/-- At a retained step, a concrete actual chart preserves the ENTIRE
NEW saturated atomic palette, not only OLD blocks: every optional NEW
atom on every child pair is classified, on every pair of chart vertices.
The two occupancy conditions are actual next child-class predicates. -/
theorem OriginalActualNextQuotientChart.newAtomicPalette
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
    {V : Type z} (old : V → Sigma B.Point) (bits : V → ZMod 2)
    (C : OriginalActualNextQuotientChart A B P (P.parent r)
      (fun i => hOne (P.parent r) i) E Kroot phase old bits) :
    let N := SingleStep.successor B phase
    let R := SingleStep.projection B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i := fun i => hOne (P.parent r) i
    let S := currentOriginalExactSetoid A N (P.compose R) (P.parent r) hBase E
    ∀ (c d : N.Sorts) (a : Option (N.source.Atom c d)) (v w : V),
      originalCurrentExactSaturatedColour A N (P.compose R)
        (P.parent r) hBase E ⟨c,d,a⟩ (C.point v) (C.point w) ↔
      (∃ x : N.Point c, S.r (C.point v) ⟨c,x⟩) ∧
      (∃ y : N.Point d, S.r (C.point w) ⟨d,y⟩) ∧
      originalCurrentExactSaturatedColour A B P (P.parent r) hBase E
        ⟨c.1,d.1,a.map (R.atom c d)⟩ (old v) (old w) := by
  intro N R hBase S c d a v w
  have h := originalRetainedActualNextSaturatedColour_factorization
    A B P transport tp hOne Kroot phase E hE c d a (C.point v) (C.point w)
  have hOld := originalCurrentExactSaturatedColour_taggedColour_iff
    A B P (P.parent r) hBase E
      ⟨c.1,d.1,a.map (R.atom c d)⟩
      (R.project (C.point v)) (R.project (C.point w))
      (old v) (old w) (C.fine v w)
  exact h.trans (and_congr_right fun _ => and_congr_right fun _ => hOld)

end
end CCO.ExactEPGeometry
