import CCO.ExactEPGeometry.OriginalRetainedOffsetGraph
import Mathlib.Tactic.Abel

/-!
# B062 C81: both genuine retained offset graphs occur on every parent

For the actual homogeneous full-character SourcePhase and its genuine
full reached component, EVERY active parent permits BOTH phase bits.
The source marked-age realization ensures that each corresponding
successor child sort is inhabited.

Fix a reached anchor a of one actual original E-occupancy component,
with ORIGINAL full RAW-exact E below the SAME source-selected old gate.
Its two bits give two DISTINCT actual successor E-occupancy classes.
Every real child in the component lies in exactly the anchor class
specified by epsilon+gamma, and each of the two anchor classes
has a real child over EVERY parent in that component.

The full reachability and per-class occupancy are previously proved
C49, C77-C81 sources. This constructs no invented labelled quotient
seed and assumes no quotient SAP or group action section.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry

noncomputable section

/-- Every bit is valid at a REAL reached current parent.
Inactive parents are handled separately by the genuine source
mask, and are never silently included in this constructor. -/
noncomputable def originalRetainedActiveBit
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot) (z : Bit) :
    UnarySource.β (SingleStep.identification B phase) b.val := by
  refine ⟨z,?_⟩
  change phase.validBit b.val z
  intro hinactive
  exact False.elim (hinactive b.property)

/-- BOTH true children of every active parent contain real points
in the actual homogeneous successor source, by the SAME provider
used for the source's full marked-age construction. -/
theorem original_retained_active_child_inhabited
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot) (z : Bit) :
    Nonempty ((SingleStep.successor B phase).Point
      ⟨b.val,originalRetainedActiveBit B Kroot phase b z⟩) :=
  (SingleStep.successor B phase).source.nonemptySort _

/-- At any reached anchor a, its two REAL occupied children carry
different original E-occupancy classes. Their separation follows
from I_aa=K_a and the genuine SourcePhase character identity,
not from pretending E itself is logical equality. -/
theorem original_retained_anchor_children_distinct_E_occupancy
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
    (a : Reached B.source Kroot) :
    ¬ (originalExactOccupancySetoid
      A (SingleStep.successor B phase)
      (P.compose (SingleStep.projection B phase))
      (P.parent r) (fun i => hOne (P.parent r) i) E).r
        ⟨a.val,originalRetainedActiveBit B Kroot phase a (0 : Bit)⟩
        ⟨a.val,originalRetainedActiveBit B Kroot phase a (1 : Bit)⟩ := by
  intro hOcc
  let J := originalExactOccupancySetoid
    A B P (P.parent r) (fun i => hOne (P.parent r) i) E
  have hBit := (original_retained_children_occupancy_iff
    A B P transport tp hOne Kroot phase E hE a a
    (J.refl a.val)
    (originalRetainedActiveBit B Kroot phase a (0 : Bit))
    (originalRetainedActiveBit B Kroot phase a (1 : Bit))).mp hOcc
  have hZero := original_retained_anchor_gamma_zero
    A B P transport tp hOne Kroot phase E hE a
  rw [hZero] at hBit
  have hContr : (1 : Bit) = 0 := by
    simpa only [originalRetainedActiveBit, zero_add] using hBit
  exact (by decide : (1 : Bit) ≠ 0) hContr

/-- For EVERY ACTUAL successor child of b in the retained E-component,
there is a real E-supported child above the selected anchor a, with
its bit exactly epsilon+gamma_b. The existence is not merely a
formal bit comparison: C81 constructs the actual original E-pair. -/
theorem original_retained_every_child_hits_corrected_anchor
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
    (a b : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).r
      b.val a.val)
    (ε : UnarySource.β (SingleStep.identification B phase) b.val) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    ∃ η : UnarySource.β (SingleStep.identification B phase) a.val,
      η.val = ε.val + phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b a hba) ∧
      (originalExactOccupancySetoid
        A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase))
        (P.parent r) (fun i => hOne (P.parent r) i) E).r
          ⟨b.val,ε⟩ ⟨a.val,η⟩ := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let γ := phase.character.value
    (original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b a hba)
  let η := originalRetainedActiveBit B Kroot phase a (ε.val + γ)
  refine ⟨η,rfl,?_⟩
  exact (original_retained_children_occupancy_iff
    A B P transport tp hOne Kroot phase E hE b a hba ε η).mpr rfl

/-- Conversely, each of the TWO genuinely realized anchor-child
E-occupancy classes has an E-supported child over EVERY original
E-supported active parent b. This is the surjectivity/projection
claim for BOTH offset graphs, not a representative-only assertion. -/
theorem original_retained_each_anchor_bit_hits_every_parent
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
    (a b : Reached B.source Kroot)
    (hba : (originalExactOccupancySetoid
      A B P (P.parent r) (fun i => hOne (P.parent r) i) E).r
      b.val a.val)
    (z : Bit) :
    letI := Reached.groupoid B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) (A := Kroot)
    ∃ ε : UnarySource.β (SingleStep.identification B phase) b.val,
      ε.val = z + phase.character.value
        (original_retained_identity_arrow
          A B P transport tp hOne Kroot E hE b a hba) ∧
      (originalExactOccupancySetoid
        A (SingleStep.successor B phase)
        (P.compose (SingleStep.projection B phase))
        (P.parent r) (fun i => hOne (P.parent r) i) E).r
          ⟨b.val,ε⟩
          ⟨a.val,originalRetainedActiveBit B Kroot phase a z⟩ := by
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  let γ := phase.character.value
    (original_retained_identity_arrow
      A B P transport tp hOne Kroot E hE b a hba)
  let ε := originalRetainedActiveBit B Kroot phase b (z + γ)
  let η := originalRetainedActiveBit B Kroot phase a z
  have hDouble : ∀ v : ZMod 2, v + v = 0 := by decide
  refine ⟨ε,rfl,?_⟩
  apply (original_retained_children_occupancy_iff
    A B P transport tp hOne Kroot phase E hE b a hba ε η).mpr
  change z = (z + γ) + γ
  calc
    z = z + 0 := (add_zero _).symm
    _ = z + (γ + γ) := by rw [hDouble]
    _ = (z + γ) + γ := by abel

end
end CCO.ExactEPGeometry
