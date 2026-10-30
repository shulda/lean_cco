import CCO.RankInduction.JointGeometry

/-! All projected original source points remain exact shadows on the
fixed joint carrier. One ORIGINAL point supplies all its coordinates. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master
open Owners.Joint MIGeometry ParityHasse.Original FinitePackets.Normalization RealClosure.Bounds

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (normalized : NoFiniteExactKernel S)
variable {A0 : Set M} {safe : Set (S.Atom () ())}
variable (F : SourceStage S H cco normalized A0 safe)

local instance jointInputsCoreInvariant (D : Direction S) : Invariant G (factorCore S H cco D).val :=
  exactInvariant S H cco (factorCore S H cco D)
local instance jointInputsOwnerInvariant (D : Direction S) :
    Invariant G (factorOwner S H cco normalized D).val :=
  exactInvariant S H cco (factorOwner S H cco normalized D)
local instance jointInputsJointInvariant : Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)

def stageTupleInput : Set (StageTuple S H cco normalized F) :=
  (jointGeometry S H cco normalized).point F.master.carrier
    (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) ⁻¹' A0

def stageOriginalTuple (finiteA : A0.Finite) (a : A0) : StageTuple S H cco normalized F :=
  (stageTupleEquiv S H cco normalized F).symm
    ⟨a.val, stage_original_contains S H cco normalized F finiteA a.property⟩

theorem stageOriginalTuple_point (finiteA : A0.Finite) (a : A0) :
    (jointGeometry S H cco normalized).point F.master.carrier
      (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)
      (stageOriginalTuple S H cco normalized F finiteA a) = a.val :=
  congrArg Subtype.val ((stageTupleEquiv S H cco normalized F).apply_symm_apply _)

theorem stageOriginalTuple_coordinate (finiteA : A0.Finite) (a : A0) (D : Direction S) :
    ((stageOriginalTuple S H cco normalized F finiteA a).val D).val =
      (Quotient.mk'' a.val : Quotient (factorCore S H cco D).val) := by
  have h := (jointGeometry S H cco normalized).point_coordinate F.master.carrier
    (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)
    (stageOriginalTuple S H cco normalized F finiteA a) D
  exact h.symm.trans (congrArg (Quotient.mk'' : M → Quotient (factorCore S H cco D).val)
    (stageOriginalTuple_point S H cco normalized F finiteA a))

theorem stageOriginalTuple_input (finiteA : A0.Finite) (a : A0) :
    stageOriginalTuple S H cco normalized F finiteA a ∈ stageTupleInput S H cco normalized F := by
  change (jointGeometry S H cco normalized).point _ _ _ _ ∈ A0
  rw [stageOriginalTuple_point]
  exact a.property

/-- The projected original input contains ALL source points of the
factor, not a separately selected coordinate representative set. -/
theorem stage_coordinate_shadow (finiteA : A0.Finite) (D : Direction S) :
    (fun w : StageTuple S H cco normalized F => w.val D) '' stageTupleInput S H cco normalized F =
      {x | x.val ∈ factorInput S H cco A0 D} := by
  ext d
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(jointGeometry S H cco normalized).point F.master.carrier
      (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) w, hw,
      (jointGeometry S H cco normalized).point_coordinate F.master.carrier
        (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) w D⟩
  · rintro ⟨a, ha, he⟩
    refine ⟨stageOriginalTuple S H cco normalized F finiteA ⟨a, ha⟩,
      stageOriginalTuple_input S H cco normalized F finiteA ⟨a, ha⟩, Subtype.ext ?_⟩
    exact (stageOriginalTuple_coordinate S H cco normalized F finiteA ⟨a, ha⟩ D).trans he

/-- The ENTIRE original owner shadow is the exact M1 input of the SAME
strict lower-rank master selected before all real partial requests. -/
theorem stage_owner_shadow (finiteA : A0.Finite) :
    ((jointGeometry S H cco normalized).ownerQuotient F.master.carrier
      (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)
      (stageOnto S H cco normalized F) (stageFullOwners S H cco normalized F)).projection ''
        stageTupleInput S H cco normalized F =
      {b | b.val ∈ (Quotient.mk'' : M → Quotient (jointKernel S H cco normalized).val) '' A0} := by
  ext b
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(jointGeometry S H cco normalized).point F.master.carrier
      (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) w, hw,
      (jointGeometry S H cco normalized).joint_point F.master.carrier
        (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)
        (stageFullOwners S H cco normalized F) w⟩
  · rintro ⟨a, ha, he⟩
    let w := stageOriginalTuple S H cco normalized F finiteA ⟨a, ha⟩
    refine ⟨w, stageOriginalTuple_input S H cco normalized F finiteA ⟨a, ha⟩, Subtype.ext ?_⟩
    have hw := (jointGeometry S H cco normalized).joint_point F.master.carrier
      (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)
      (stageFullOwners S H cco normalized F) w
    exact hw.symm.trans ((congrArg (Quotient.mk'' : M → Quotient (jointKernel S H cco normalized).val)
      (stageOriginalTuple_point S H cco normalized F finiteA ⟨a, ha⟩)).trans he)

end
end CCO.RankInduction.Factors
