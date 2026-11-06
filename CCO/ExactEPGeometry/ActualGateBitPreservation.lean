import CCO.ExactEPGeometry.CertifiedOriginalKernel
import CCO.APCharacter.SourceAge.SingleStep
import CCO.APCharacter.MaskReadout

/-!
# B062 C61: genuine active current phase gates preserve their new bit

The actual full-character SourcePhase is marked on real current points
by the SAME `SourceAge.SingleStep.identification` used in the canonical
next source. Its mask legality follows from the full marked-age limit,
not an independently chosen marking of the old source.

For ANY actual object b of its full connected `Reached` groupoid,
the identity Arrow at b is the ENTIRE exact kernel K_b. Its character
value is zero. Hence every real K_b-pair has equal actual phase bits,
by the proved source `SourcePhase.rigid_mask_iff`. We extract the
literal new child tag equality from this valid pair-mask equation.

This is the C61 one-stage gate-bit preservation obligation, not yet
the full C61–C64 induction through all original prefixes or
maximality among ALL old final-label-preserving ExactEq relations.
No quotient SAP, group section, new axiom or fictional mask provider.
-/

universe u v w t

namespace CCO.ExactEPGeometry

open APCharacter
open APCharacter.Towers
open APCharacter.SourceAge
open RigidGroupoid.Geometry

noncomputable section

/-- An ACTUAL current phase kernel pair has identical pulled-back bits
in ANY genuine full marked-age identification for the SAME source
phase. Proof is via true marked-age pair legality and the character
value of the REAL current gate's identity Arrow. -/
theorem source_phase_gate_mark_constant
    (B : CurrentSource.{u,v,w,t})
    {i : B.Sorts} {K : Kernel B.source i}
    (P : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (I : UnarySource.Identification B.source B.homogeneous
      (P.completion_property B.cco))
    (b : Reached B.source K)
    (x y : B.Point b.val)
    (hxy : (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).rel x y) :
    UnarySource.mark I ⟨b.val,x⟩ =
      UnarySource.mark I ⟨b.val,y⟩ := by
  let ε : Bit := UnarySource.mark I ⟨b.val,x⟩
  let η : Bit := UnarySource.mark I ⟨b.val,y⟩
  let C := exactCalculus_of_homogeneous_CCO
    B.source B.homogeneous B.cco
  let Kb := Reached.kernel B.homogeneous C b
  have hLegal : P.allows (B.source.colour x y) ε η :=
    (UnarySource.global_marking I).2 ⟨b.val,x⟩ ⟨b.val,y⟩
  letI := Reached.groupoid B.homogeneous C (A := K)
  have hAllowed := (P.rigid_mask_iff b b (Arrow.id Kb)
    x y hxy ε η).mp hLegal
  have hZero : P.character.value (Arrow.id Kb) = 0 :=
    P.character.map_id b
  have hBit : η = ε := by
    simpa only [hZero,add_zero] using hAllowed.2.2
  exact hBit.symm

/-- Source C61 for the LITERAL children of the canonical AP-only
full-character successor, whose entire-carrier identification and
valid unary child tags were constructed by the accepted source.
No independent tag or global marking is chosen here. -/
theorem canonical_phase_gate_preserves_child_tag
    (B : CurrentSource.{u,v,w,t})
    {i : B.Sorts} {K : Kernel B.source i}
    (P : SourcePhase B.source B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) K)
    (b : Reached B.source K)
    (x y : B.Point b.val)
    (hxy : (Reached.kernel B.homogeneous
      (exactCalculus_of_homogeneous_CCO
        B.source B.homogeneous B.cco) b).rel x y) :
    UnarySource.tag (SingleStep.identification B P) b.val x =
      UnarySource.tag (SingleStep.identification B P) b.val y := by
  apply Subtype.ext
  exact source_phase_gate_mark_constant B P
    (SingleStep.identification B P) b x y hxy

end
end CCO.ExactEPGeometry
