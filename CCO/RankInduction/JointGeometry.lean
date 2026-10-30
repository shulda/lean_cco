import CCO.RankInduction.SourceStage
import CCO.RankInduction.AmalgamationBridge
import CCO.Owners.Joint.Source
import CCO.MIGeometry.ClosureBands
import CCO.AclOwners.ClosedPreimages

/-! The ALL-compatible actual original carrier and its entire closure
target, using one already materialized strict master and factor system. -/

universe v w t
namespace CCO.RankInduction.Factors
noncomputable section
open RawExact ExactCRT CanonicalQuotients Owners.Product Owners.Provider Owners.Master
open Owners.Joint MIGeometry ParityHasse.Original FinitePackets.Normalization
open RealClosure.Bounds AclOwners

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] [Countable M] [DecidableEq M]
variable (H : HomogeneousSource S G) (cco : SemanticCCO.{0,v,v,w} S)
variable (normalized : NoFiniteExactKernel S)

local instance jointAssemblyCoreInvariant (D : Direction S) : Invariant G (factorCore S H cco D).val :=
  exactInvariant S H cco (factorCore S H cco D)
local instance jointAssemblyOwnerInvariant (D : Direction S) :
    Invariant G (factorOwner S H cco normalized D).val :=
  exactInvariant S H cco (factorOwner S H cco normalized D)
local instance jointAssemblyJointInvariant : Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)

/-- Every ambient tuple and original fine colour is supplied by the
accepted exact-source CRT, with actual meet-Id and the exact JOG gate. -/
def jointGeometry := actualGeometry S H cco (factorCore S H cco)
  (factorOwner S H cco normalized)
  (core_le_owner S H (semanticCCO_change_universe S cco) normalized)
  (cores_separate S H (semanticCCO_change_universe S cco) normalized)
  (join_gate S H (semanticCCO_change_universe S cco) normalized)

variable {A0 : Set M} {safe : Set (S.Atom () ())}
variable (F : SourceStage S H cco normalized A0 safe)

def stageCarriers (D : Direction S) := (F.component D).carrier

theorem stageOver (D : Direction S) (d : stageCarriers S H cco normalized F D) :
    (jointGeometry S H cco normalized).own D d.val ∈
      (jointGeometry S H cco normalized).OwnerImage F.master.carrier D :=
  (F.component D).over d

theorem stageOnto (D : Direction S) :
    Function.Surjective ((jointGeometry S H cco normalized).finiteOwn F.master.carrier
      (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) D) :=
  (F.component D).onto

/-- M4 identifies this SAME finite joint master with the entire compatible
owner tuple set; individual coordinate surjectivity is insufficient. -/
theorem stageFullOwners :
    FullOwners ((jointGeometry S H cco normalized).finiteDiagram F.master.carrier) := by
  classical
  let : Fintype (Direction S) := Fintype.ofFinite _
  intro b compatible
  obtain ⟨c, hc, eqc⟩ := master_realizes_images S H cco (jointKernel S H cco normalized)
    F.master (factorOwner S H cco normalized) (jointKernel_le_owner S H cco normalized)
    (fun D => (b D).val) (fun D => (b D).property) compatible
  exact ⟨⟨c, hc⟩, fun D => Subtype.ext (eqc D)⟩

def stageCarrier : Set M :=
  (jointGeometry S H cco normalized).inducedCarrier (stageCarriers S H cco normalized F)

abbrev StageTuple := (jointGeometry S H cco normalized).Witness F.master.carrier
  (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)

def stageTupleEquiv : StageTuple S H cco normalized F ≃ stageCarrier S H cco normalized F :=
  (jointGeometry S H cco normalized).pointCarrierEquiv F.master.carrier
    (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)

theorem stage_finite : (stageCarrier S H cco normalized F).Finite := by
  let : ∀ D : Direction S, Finite (stageCarriers S H cco normalized F D) :=
    fun D => (F.component D).ordinary.finite.to_subtype
  exact Set.finite_coe_iff.mpr ((jointGeometry S H cco normalized).inducedCarrier_finite
    (stageCarriers S H cco normalized F))

include normalized in
/-- The WHOLE absolute target is the full compatible product of all
factor closures, including every original point over its coordinates. -/
theorem stage_target_identity (finiteA : A0.Finite) :
    FiniteLift.aclSet G A0 = {x | ∀ D : Direction S,
      (Quotient.mk'' x : Quotient (factorCore S H cco D).val) ∈
        FiniteLift.aclSet G (factorInput S H cco A0 D)} := by
  classical
  have h := hat_closure_pullback S H (semanticCCO_change_universe S cco) normalized finiteA.toFinset
  simp only [← FiniteLift.aclSet_finset, Finset.coe_image, Set.Finite.coe_toFinset] at h
  exact h

theorem stage_contains (finiteA : A0.Finite) :
    FiniteLift.aclSet G A0 ⊆ stageCarrier S H cco normalized F := by
  intro x hx D
  rw [stage_target_identity S H cco normalized finiteA] at hx
  exact (F.component D).ordinary.closure (hx D)

theorem stage_original_contains (finiteA : A0.Finite) :
    A0 ⊆ stageCarrier S H cco normalized F :=
  (FiniteLift.subset_aclSet G A0).trans (stage_contains S H cco normalized F finiteA)

/-- Absolute closure of every chosen factor gives absolute closure of the
literal ALL-coordinate inverse intersection, rather than packet closure
being used as a substitute in the original multi-direction source. -/
theorem stage_closed : FiniteLift.aclSet G (stageCarrier S H cco normalized F) =
    stageCarrier S H cco normalized F := by
  classical
  ext x
  constructor
  · intro hx
    rw [stage_target_identity S H cco normalized (stage_finite S H cco normalized F)] at hx
    intro D
    have subset : factorInput S H cco (stageCarrier S H cco normalized F) D ⊆
        (F.component D).carrier := by
      rintro q ⟨a, ha, rfl⟩
      exact ha D
    have h := FiniteLift.aclSet_mono G subset (hx D)
    rw [(F.component D).closed] at h
    exact h
  · intro hx
    exact FiniteLift.subset_aclSet G (stageCarrier S H cco normalized F) hx

theorem stage_points (D : Direction S) :
    GroupActions.PrescribedLift
      ((jointGeometry S H cco normalized).factorAction F.master.carrier
        (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)
        (stageOnto S H cco normalized F) D)
      ((jointGeometry S H cco normalized).finiteOwn F.master.carrier
        (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) D) :=
  (F.component D).points

end
end CCO.RankInduction.Factors
