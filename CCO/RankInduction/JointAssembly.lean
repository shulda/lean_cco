import CCO.RankInduction.JointRoots

/-! The complete actual multi-factor assembly from a materialized source
stage. Its principal caller constructs that stage from the strict lower
master and the normalized relative-MI theorem; no component callback is a
new hypothesis of the source rank theorem. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open ParityHasse.Original FinitePackets.Normalization RealClosure.Bounds

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (normalized : NoFiniteExactKernel S)
variable {A0 : Set M} {safe : Set (S.Atom () ())}
variable (F : SourceStage S H cco normalized A0 safe)

/-- One literal finite original W has ALL original partial-map extensions,
rooted unsafe transport into the ENTIRE absolute target, and absolute
closure on that SAME W. Full group/owner identities are supplied by the
preceding actual assembly, not by a source-level provider assumption. -/
theorem joint_stage_witness (finiteA : A0.Finite) (many : 2 ≤ directionCount S)
    (amalgamate : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe)) :
    Witness S G safe A0 (stageCarrier S H cco normalized F) ∧
      FiniteLift.aclSet G (stageCarrier S H cco normalized F) = stageCarrier S H cco normalized F := by
  constructor
  · exact {
      finite := stage_finite S H cco normalized F
      closure := stage_contains S H cco normalized F finiteA
      extensions := stage_extensions S H cco normalized F finiteA
      roots := stage_roots S H cco normalized F finiteA many amalgamate }
  · exact stage_closed S H cco normalized F

include H cco normalized F in
theorem joint_stage_exists (finiteA : A0.Finite) (many : 2 ≤ directionCount S)
    (amalgamate : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe)) :
    ∃ W : Set M, Witness S G safe A0 W ∧ FiniteLift.aclSet G W = W :=
  ⟨stageCarrier S H cco normalized F,
    joint_stage_witness S H cco normalized F finiteA many amalgamate⟩

end
end CCO.RankInduction.Factors
