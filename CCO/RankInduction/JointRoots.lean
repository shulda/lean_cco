import CCO.RankInduction.JointUnsafe
import CCO.RankInduction.JointExtensions
import CCO.Owners.Joint.ExceptionalFinite

/-! One ORIGINAL old root and one whole master action synchronize the
exceptional rooted factor transport with every remaining WHOLE packet. -/

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

local instance jointRootsCoreInvariant (D : Direction S) : Invariant G (factorCore S H cco D).val :=
  exactInvariant S H cco (factorCore S H cco D)
local instance jointRootsOwnerInvariant (D : Direction S) :
    Invariant G (factorOwner S H cco normalized D).val :=
  exactInvariant S H cco (factorOwner S H cco normalized D)
local instance jointRootsJointInvariant : Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)

/-- The exceptional factor is retained exactly. Master M3 first lifts
its ENTIRE owner component and then corrects the joint root in the kernel.
All other factor actions transport their WHOLE packets to that ONE old
original point's coordinates. -/
theorem stage_tuple_roots (finiteA : A0.Finite) (many : 2 ≤ directionCount S)
    (amalgamate : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (Z : Set (StageTuple S H cco normalized F))
    (hZ : FiniteLift.Unsafe (fun x y => S.menuRel safe
      (stagePoint S H cco normalized F x) (stagePoint S H cco normalized F y)) Z)
    (z : StageTuple S H cco normalized F) (hz : z ∈ Z) :
    ∃ α : OrbitalAut G M (stagePoint S H cco normalized F),
      (∀ x ∈ Z, stagePoint S H cco normalized F (α.val x) ∈ FiniteLift.aclSet G A0) ∧
      stagePoint S H cco normalized F (α.val z) ∈ A0 := by
  let P := jointGeometry S H cco normalized
  let D := stageCarriers S H cco normalized F
  let over := stageOver S H cco normalized F
  let onto := stageOnto S H cco normalized F
  let full := stageFullOwners S H cco normalized F
  obtain ⟨e, concentrated⟩ := stage_exceptional_factor S H cco normalized F many amalgamate Z hZ
  obtain ⟨β, target, root⟩ := (F.component e).ordinary.roots
    ((fun w : StageTuple S H cco normalized F => w.val e) '' Z)
    (stage_factor_unsafe S H cco normalized F Z hZ e) (z.val e) ⟨z, hz, rfl⟩
  have exceptionalZ (x : StageTuple S H cco normalized F) (hx : x ∈ Z) :
      β.val (x.val e) ∈ stageFactorTarget S H cco normalized F e :=
    target (x.val e) ⟨x, hx, rfl⟩
  have exceptionalRoot : β.val (z.val e) ∈
      (fun w : StageTuple S H cco normalized F => w.val e) '' stageTupleInput S H cco normalized F := by
    obtain ⟨a, ha, hroot⟩ := root
    refine ⟨stageOriginalTuple S H cco normalized F finiteA ⟨a, ha⟩,
      stageOriginalTuple_input S H cco normalized F finiteA ⟨a, ha⟩, Subtype.ext ?_⟩
    exact (stageOriginalTuple_coordinate S H cco normalized F finiteA ⟨a, ha⟩ e).trans hroot
  obtain ⟨α, _retain, root, all⟩ := P.exceptional_finite F.master.carrier D over onto full
    (stage_points S H cco normalized F) e (stageTupleInput S H cco normalized F) Z z hz
    (stageFactorTarget S H cco normalized F) (stageFactorPacket S H cco normalized F)
    (stage_packet_invariant S H cco normalized F)
    (stage_target_packet_closed S H cco normalized F finiteA)
    (fun i ne x hx => concentrated i ne z hz x hx) β exceptionalZ exceptionalRoot
    (stage_joint_m3 S H cco normalized F e)
  refine ⟨α, ?_, root⟩
  intro x hx
  rw [stage_target_identity S H cco normalized finiteA]
  intro i
  rw [stagePoint_coordinate S H cco normalized F (α.val x) i]
  exact all x hx i

/-- The synchronized transport acts on the literal original induced W.
The selected root lands in ORIGINAL A0; the entire unsafe clique lands in
the WHOLE absolute target, not merely chosen coordinate representatives. -/
theorem stage_roots (finiteA : A0.Finite) (many : 2 ≤ directionCount S)
    (amalgamate : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (Z : Set (stageCarrier S H cco normalized F))
    (hZ : FiniteLift.Unsafe (fun x y : stageCarrier S H cco normalized F => S.menuRel safe x.val y.val) Z)
    (z : stageCarrier S H cco normalized F) (hz : z ∈ Z) :
    ∃ β : OrbitalAut G M (Subtype.val : stageCarrier S H cco normalized F → M),
      (∀ x ∈ Z, (β.val x).val ∈ FiniteLift.aclSet G A0) ∧ (β.val z).val ∈ A0 := by
  let e := stageTupleEquiv S H cco normalized F
  let Zt := e ⁻¹' Z
  have unsafeTuple : FiniteLift.Unsafe (fun x y => S.menuRel safe
      (stagePoint S H cco normalized F x) (stagePoint S H cco normalized F y)) Zt := by
    constructor
    · obtain ⟨x, hx⟩ := hZ.1
      exact ⟨e.symm x, by change e (e.symm x) ∈ Z; simpa only [Equiv.apply_symm_apply] using hx⟩
    · intro x hx y hy ne hs
      exact hZ.2 (e x) hx (e y) hy (fun he => ne (e.injective he)) hs
  have selected : e.symm z ∈ Zt := by
    change e (e.symm z) ∈ Z
    simpa only [Equiv.apply_symm_apply] using hz
  obtain ⟨α, target, root⟩ := stage_tuple_roots S H cco normalized F finiteA many amalgamate
    Zt unsafeTuple (e.symm z) selected
  let β := (jointGeometry S H cco normalized).inducedAutCongr F.master.carrier
    (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) α
  have motion (x : stageCarrier S H cco normalized F) :
      (β.val x).val = stagePoint S H cco normalized F (α.val (e.symm x)) := by
    have h := (jointGeometry S H cco normalized).inducedAutCongr_apply F.master.carrier
      (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) α (e.symm x)
    change β.val (e (e.symm x)) = e (α.val (e.symm x)) at h
    rw [Equiv.apply_symm_apply] at h
    exact congrArg Subtype.val h
  refine ⟨β, ?_, ?_⟩
  · intro x hx
    have member : e.symm x ∈ Zt := by
      change e (e.symm x) ∈ Z
      simpa only [Equiv.apply_symm_apply] using hx
    exact Eq.mpr (congrArg (fun a : M => a ∈ FiniteLift.aclSet G A0) (motion x))
      (target (e.symm x) member)
  · exact Eq.mpr (congrArg (fun a : M => a ∈ A0) (motion z)) root

end
end CCO.RankInduction.Factors
