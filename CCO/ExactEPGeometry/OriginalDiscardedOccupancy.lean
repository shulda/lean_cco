import CCO.ExactEPGeometry.OriginalDiscardedChildOccupancy

/-!
# B062 C76: discarded phase preserves the EXACT occupancy partition

Fix ONE original AP+HOM CCO sort and a true full-character SourcePhase of
a current source B with its ACTUAL original-to-current reduct P and
proved two-way exact/TP certificates. An original FULL RAW-exact E is
not below the TRUE selected greatest original exact gate.

The already proved C73–C75 source theorem says every real E-class in
EACH active parent meets BOTH new legal children; inactive parents
have exactly ONE valid child bit. Therefore given ANY actual source
child c and target child d, original-E support between their old
current parents is equivalent to original-E support between those
TWO EXACT successor sorts.

This is stronger than the existential statement that one class somewhere
uses both bits: for EVERY actual point in the source child, old occupancy
gives a real related point in the target parent; C75 adjusts that
specific E-class into the SPECIFIED valid target child. Distinct
old occupancy classes never merge, and the same class does not split.

No quotient source is postulated, no SAP, arbitrary quotient actions,
unrealized label, or independent bit selections are assumed.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- C76 real classwise extension: if two old current parent TYPES lie
in the same E-occupancy class, then EVERY specific point of ANY source
successor child c has a SAME-original-E-class representative in ANY
chosen actual target child d. This uses C73/C75 for active targets and
the true unique legal bit in inactive targets. -/
theorem original_discarded_class_hits_every_supported_child
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
    (c d : (SingleStep.successor B phase).Sorts)
    (hOld : (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).r c.1 d.1)
    (x : (SingleStep.successor B phase).Point c) :
    ∃ y : (SingleStep.successor B phase).Point d,
      (currentOriginalExactSetoid
        A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase))
        (P.parent r) (fun i => hOne (P.parent r) i) E).r
          (⟨c,x⟩ : Sigma (SingleStep.successor B phase).Point)
          (⟨d,y⟩ : Sigma (SingleStep.successor B phase).Point) := by
  classical
  let I := SingleStep.identification B phase
  let hBase : ∀ i : A.Sorts, P.parent r = i :=
    fun i => hOne (P.parent r) i
  let J := currentOriginalExactSetoid A B P (P.parent r) hBase E
  obtain ⟨y₀,hXY₀⟩ :=
    (originalExactClass_occupies_supported_type
      A B P (P.parent r) hBase E c.1 d.1 x.val).mp hOld
  have hSuccessor (z : B.Point d.1)
      (hXZ : J.r (⟨c.1,x.val⟩ : Sigma B.Point)
          (⟨d.1,z⟩ : Sigma B.Point))
      (hTagZ : UnarySource.tag I d.1 z = d.2) :
      ∃ y : (SingleStep.successor B phase).Point d,
        (currentOriginalExactSetoid
          A (SingleStep.successor B phase)
          (P.compose (SingleStep.projection B phase))
          (P.parent r) hBase E).r
          (⟨c,x⟩ : Sigma (SingleStep.successor B phase).Point)
          (⟨d,y⟩ : Sigma (SingleStep.successor B phase).Point) := by
    refine ⟨⟨z,hTagZ⟩,?_⟩
    change (originalExactGlobalRelation A (P.parent r) hBase E)
      (P.project ⟨c.1,x.val⟩) (P.project ⟨d.1,z⟩)
    exact hXZ
  by_cases hActive : Nonempty (Bridge B.source Kroot d.1)
  · let b : Reached B.source Kroot := ⟨d.1,hActive⟩
    by_cases hBit : UnarySource.tag I d.1 y₀ = d.2
    · exact hSuccessor y₀ hXY₀ hBit
    · obtain ⟨z,hEz,hFlip⟩ :=
        original_discarded_each_active_class_opposite_child
          A B P transport tp hOne Kroot phase E hNot b y₀
      have hMarkNe :
          UnarySource.mark I ⟨d.1,y₀⟩ ≠ d.2.val := by
        intro hEq
        exact hBit (Subtype.ext hEq)
      have hOther : d.2.val =
          UnarySource.mark I ⟨d.1,y₀⟩ + (1 : Bit) :=
        (by decide : ∀ a b : Bit, a ≠ b → b = a + (1 : Bit))
          _ _ hMarkNe
      have hMarkZ :
          UnarySource.mark I ⟨d.1,z⟩ = d.2.val :=
        hFlip.trans hOther.symm
      have hTagZ : UnarySource.tag I d.1 z = d.2 :=
        Subtype.ext hMarkZ
      have hLocal :
          (originalExactOnCurrentSort
            A B P transport (P.parent r) hBase E d.1) y₀ z := by
        change (PrefixExactRestriction.rho A B P transport d.1
          (oldExactEqCast A.source
            (hOne (P.parent r) (P.parent d.1)).symm E)) y₀ z
        exact hEz
      have hYZ : J.r (⟨d.1,y₀⟩ : Sigma B.Point)
          (⟨d.1,z⟩ : Sigma B.Point) :=
        (originalExactOnCurrentSort_iff
          A B P transport (P.parent r) hBase E d.1 y₀ z).mp hLocal
      have hXZ : J.r (⟨c.1,x.val⟩ : Sigma B.Point)
          (⟨d.1,z⟩ : Sigma B.Point) :=
        J.trans hXY₀ hYZ
      exact hSuccessor z hXZ hTagZ
  · have hValid : phase.validBit d.1
        (UnarySource.mark I ⟨d.1,y₀⟩) :=
      (UnarySource.global_marking I).1 ⟨d.1,y₀⟩
    have hBitEq : d.2.val =
        UnarySource.mark I ⟨d.1,y₀⟩ :=
      phase.inactive_bit_unique hActive d.2.property hValid
    have hTagZ : UnarySource.tag I d.1 y₀ = d.2 :=
      Subtype.ext hBitEq.symm
    exact hSuccessor y₀ hXY₀ hTagZ

/-- C76 exact semantic statement: the actual E-support relation on
successor sort NAMES is the inverse image of the OLD type support
relation along the true parent projection. Thus no old occupancy
class is split by a discarded bit, and distinct old classes never
coalesce. The proof constructs a point in EVERY specified child,
not merely some child from a labelled quotient seed. -/
theorem original_discarded_successor_occupancy_iff
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
    (c d : (SingleStep.successor B phase).Sorts) :
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
    let x : (SingleStep.successor B phase).Point c :=
      Classical.choice ((SingleStep.successor B phase).source.nonemptySort c)
    obtain ⟨y,hXY⟩ :=
      original_discarded_class_hits_every_supported_child
        A B P transport tp hOne Kroot phase E hNot c d hOld x
    exact ⟨x,y,hXY⟩

end
end CCO.ExactEPGeometry
