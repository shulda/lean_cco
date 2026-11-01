import CCO.ExactEPGeometry.ActualGateBitMaximality
import CCO.ExactEPGeometry.OriginalOneSortExactDescent

/-!
# B062 C74–C75: EVERY real E-class meets the opposite actual child

The genuine AP-only SourcePhase contains the FULL reached rigid
groupoid, its real odd Arrow at EACH active reached sort and its
character of value 1. Its maximality/dominance is about ALL genuine
current FULL RAW-exact equivalences strictly above the gate, not
arbitrary invariant equivalences or a selected list of generators.

If an actual current full-exact E is not below the genuine gate K_b,
the exact join E∨K_b strictly exceeds K_b and therefore contains the
ENTIRE odd Arrow relation at b. For EVERY real point x in that
parent, old exact seriality finds a real odd neighbour z.
The genuine represented join factors x E y K_b z. Since K_b
preserves the actual new bit and the odd Arrow reverses it,
y lies in the SAME E-class as x but in the opposite new child.

This proves class-by-class occupancy, not just the existence of
some cross-bit E-pair. No quotient SAP, global action section,
unsupported strong amalgamation or fake empty atomic meet is used.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.SourceAge
open APCharacter.Towers
open RigidGroupoid.Geometry
open CCO.ParityHasse.Original

noncomputable section

/-- C74–C75 at any actual active reached parent of the full connected
current phase: for EVERY real x, if a genuinely FULL RAW-exact E
is not below its real current gate, a real E-equivalent y exists with
the OPPOSITE valid canonical child bit. The returned y is in the
same current named parent, and the literal bit formula witnesses
the exact phase-one flip (not a nominal label). -/
theorem current_not_below_gate_each_class_opposite_bit
    (B : CurrentSource.{u,v,w,t})
    {r : B.Sorts} (Kroot : Kernel B.source r)
    (phase : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) Kroot)
    (b : Reached B.source Kroot)
    (E : ExactEq B.source b.val)
    (hNot : ¬ E ≤ current_kernel_exact_eq B
      (Reached.kernel B.homogeneous
        (exactCalculus_of_homogeneous_CCO
          B.source B.homogeneous B.cco) b))
    (x : B.Point b.val) :
    ∃ y : B.Point b.val, E x y ∧
      UnarySource.mark (SingleStep.identification B phase) ⟨b.val,y⟩ =
        UnarySource.mark (SingleStep.identification B phase) ⟨b.val,x⟩ +
          (1 : Bit) := by
  classical
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let K := Reached.kernel B.homogeneous C b
  let KF : ExactEq B.source b.val := current_kernel_exact_eq B K
  let Z : ExactEq B.source b.val :=
    ExactEq.sup B.homogeneous B.cco E KF
  let L : Kernel B.source b.val := ⟨Z.val.val,Z.property⟩
  have hJoin (a d : B.Point b.val) :
      Z a d ↔ ∃ m : B.Point b.val, E a m ∧ K.rel m d :=
    sup_relation_iff B.source B.homogeneous E.val KF.val a d
  have hKleL : K ≤ L := by
    intro a d had
    exact (hJoin a d).mpr ⟨a,E.val.val.refl a,had⟩
  have hNotLleK : ¬ L ≤ K := by
    intro hLK
    apply hNot
    intro a d had
    apply hLK
    exact (hJoin a d).mpr ⟨d,had,K.setoid.refl d⟩
  have hStrict : K < L :=
    lt_iff_le_and_ne.mpr ⟨hKleL,fun he => hNotLleK (le_of_eq he.symm)⟩
  let T := phase.atSort b
  have hDominant : Dominant K T := phase.atSort_dominant b
  obtain ⟨z,hOdd⟩ := T.exact.serial B.source B.homogeneous x
  have hJoinXZ : L.rel x z := hDominant L hStrict x z hOdd
  obtain ⟨y,hExy,hKyz⟩ := (hJoin x z).mp hJoinXZ
  let I := SingleStep.identification B phase
  have hTagK : UnarySource.tag I b.val y = UnarySource.tag I b.val z :=
    canonical_phase_gate_preserves_child_tag B phase b y z hKyz
  have hMarkK :
      UnarySource.mark I ⟨b.val,y⟩ = UnarySource.mark I ⟨b.val,z⟩ :=
    congrArg Subtype.val hTagK
  letI := Reached.groupoid B.homogeneous C (A := Kroot)
  have hLegal :
      phase.allows (B.source.colour x z)
        (UnarySource.mark I ⟨b.val,x⟩)
        (UnarySource.mark I ⟨b.val,z⟩) :=
    (UnarySource.global_marking I).2 ⟨b.val,x⟩ ⟨b.val,z⟩
  have hMasked :=
    (phase.rigid_mask_iff b b T x z hOdd
      (UnarySource.mark I ⟨b.val,x⟩)
      (UnarySource.mark I ⟨b.val,z⟩)).mp hLegal
  have hOddOne : phase.character.value T = (1 : Bit) :=
    phase.atSort_detects b
  have hFlip :
      UnarySource.mark I ⟨b.val,z⟩ =
        UnarySource.mark I ⟨b.val,x⟩ + (1 : Bit) := by
    simpa only [hOddOne] using hMasked.2.2
  exact ⟨y,hExy,hMarkK.trans hFlip⟩

end
end CCO.ExactEPGeometry
