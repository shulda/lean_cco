import CCO.ExactEPGeometry.OriginalRetainedBothGraphs

/-!
# B062 C81: inactive retained occupancy classes have ONE unchanged lift

If the original full RAW-exact E is retained below the actual
source-selected original gate G, C77 proves that all parents in
one real E-occupancy component are either reached or inactive.

An inactive parent permits exactly ONE actual legal child bit.
For any two actual children c,d with inactive c's parent, their
original E-occupancy in the TRUE successor is EXACTLY the
old E-occupancy of their parents; the E-class C49 occupancy
theorem supplies a point in the specified inactive target child.
No quotient SAP, group section, extra marking or arbitrary
quotient descent is assumed.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- For a genuine inactive current parent, every pair of its
actually legal child tags agrees. It cannot secretly acquire
a second child under a retained original quotient. -/
theorem original_retained_inactive_child_tag_unique
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (i : B.Sorts)
    (hInactive : ¬Nonempty (Bridge B.source Kroot i))
    (ε η : UnarySource.β (SingleStep.identification B phase) i) :
    ε = η := by
  apply Subtype.ext
  exact phase.inactive_bit_unique hInactive ε.property η.property

/-- Exact C81 INACTIVE graph equation: successor E-support is
exactly the inverse image of its previous parent E-support.
Every realized target child is the unique valid inactive child;
we actually construct an E-equivalent point inside it. -/
theorem original_retained_inactive_successor_occupancy_iff
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
    (c d : (SingleStep.successor B phase).Sorts)
    (hInactive : ¬Nonempty (Bridge B.source Kroot c.1)) :
    (originalExactOccupancySetoid
      A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (fun i => hOne (P.parent r) i) E).r c d ↔
    (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).r c.1 d.1 := by
  constructor
  · rintro ⟨x,y,hXY⟩
    exact ⟨x.val,y.val,hXY⟩
  · intro hOld
    let I := SingleStep.identification B phase
    let hBase : ∀ i : A.Sorts, P.parent r = i :=
      fun i => hOne (P.parent r) i
    let x : (SingleStep.successor B phase).Point c :=
      Classical.choice ((SingleStep.successor B phase).source.nonemptySort c)
    obtain ⟨y,hXY⟩ :=
      (originalExactClass_occupies_supported_type
        A B P (P.parent r) hBase E c.1 d.1 x.val).mp hOld
    have hInactiveD : ¬Nonempty (Bridge B.source Kroot d.1) := by
      intro hActiveD
      have hActiveC : Nonempty (Bridge B.source Kroot c.1) :=
        (original_retained_occupancy_active_iff
          A B P transport tp hOne Kroot E hE
          c.1 d.1 hOld).mpr hActiveD
      exact hInactive hActiveC
    have hValidY : phase.validBit d.1
        (UnarySource.mark I ⟨d.1,y⟩) :=
      (UnarySource.global_marking I).1 ⟨d.1,y⟩
    have hTag : UnarySource.tag I d.1 y = d.2 := by
      apply Subtype.ext
      exact phase.inactive_bit_unique
        hInactiveD hValidY d.2.property
    refine ⟨x,⟨y,hTag⟩,?_⟩
    change (originalExactGlobalRelation A (P.parent r) hBase E)
      (P.project ⟨c.1,x.val⟩) (P.project ⟨d.1,y⟩)
    exact hXY

end
end CCO.ExactEPGeometry
