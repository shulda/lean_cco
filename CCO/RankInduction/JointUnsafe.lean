import CCO.RankInduction.JointInputs
import CCO.MIGeometry.FactorSafety
import CCO.RealClosure.Bounds.PacketBounds

/-! Actual unsafe original cliques and all their factor projections.
The nonexceptional factors lie in WHOLE recognizable finite packets. -/

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

local instance jointUnsafeCoreInvariant (D : Direction S) : Invariant G (factorCore S H cco D).val :=
  exactInvariant S H cco (factorCore S H cco D)
local instance jointUnsafeOwnerInvariant (D : Direction S) :
    Invariant G (factorOwner S H cco normalized D).val :=
  exactInvariant S H cco (factorOwner S H cco normalized D)
local instance jointUnsafeJointInvariant : Invariant G (jointKernel S H cco normalized).val :=
  exactInvariant S H cco (jointKernel S H cco normalized)

def stagePoint : StageTuple S H cco normalized F → M :=
  (jointGeometry S H cco normalized).point F.master.carrier
    (stageCarriers S H cco normalized F) (stageOver S H cco normalized F)

theorem stagePoint_coordinate (w : StageTuple S H cco normalized F) (D : Direction S) :
    (Quotient.mk'' (stagePoint S H cco normalized F w) : Quotient (factorCore S H cco D).val) =
      (w.val D).val :=
  (jointGeometry S H cco normalized).point_coordinate F.master.carrier
    (stageCarriers S H cco normalized F) (stageOver S H cco normalized F) w D

def stageFactorPacket (D : Direction S) : Setoid (stageCarriers S H cco normalized F D) :=
  Setoid.comap Subtype.val (finitePacket (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)).val

def stageFactorTarget (D : Direction S) : Set (stageCarriers S H cco normalized F D) :=
  {x | x.val ∈ FiniteLift.aclSet G (factorInput S H cco A0 D)}

theorem stage_original_unsafe (Z : Set (StageTuple S H cco normalized F))
    (hZ : FiniteLift.Unsafe (fun x y => S.menuRel safe
      (stagePoint S H cco normalized F x) (stagePoint S H cco normalized F y)) Z) :
    AclOwners.UnsafeClique S safe (stagePoint S H cco normalized F '' Z) := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ ne
  have neab : a ≠ b := fun he => ne (congrArg (stagePoint S H cco normalized F) he)
  cases hc : S.colour (i := ()) (j := ()) (stagePoint S H cco normalized F a)
      (stagePoint S H cco normalized F b) with
  | none => exact False.elim (ne (eq_of_heq (Sigma.mk.inj ((S.colour_none_iff _ _).mp hc)).2))
  | some c => exact ⟨c, hc, fun hs => hZ.2 a ha b hb neab ⟨c, hs, hc⟩⟩

/-- A projected clique is its actual SET of distinct factor points;
coincident projections and singleton projections cause no exception. -/
theorem stage_factor_unsafe (Z : Set (StageTuple S H cco normalized F))
    (hZ : FiniteLift.Unsafe (fun x y => S.menuRel safe
      (stagePoint S H cco normalized F x) (stagePoint S H cco normalized F y)) Z)
    (D : Direction S) :
    FiniteLift.Unsafe (fun x y : stageCarriers S H cco normalized F D =>
      (factorSource S H (semanticCCO_change_universe S cco) D).menuRel
        (factorPalette S H cco safe D) x.val y.val)
      ((fun w : StageTuple S H cco normalized F => w.val D) '' Z) := by
  refine ⟨hZ.1.image _, ?_⟩
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩ ne ⟨c, hs, hc⟩
  have neab : a ≠ b := fun he => ne (congrArg (fun w : StageTuple S H cco normalized F => w.val D) he)
  apply hZ.2 a ha b hb neab
  have projected : (factorSource S H (semanticCCO_change_universe S cco) D).colour
      (i := ()) (j := ()) (Quotient.mk'' (stagePoint S H cco normalized F a))
      (Quotient.mk'' (stagePoint S H cco normalized F b)) = some c := by
    rw [stagePoint_coordinate S H cco normalized F a D,
      stagePoint_coordinate S H cco normalized F b D]
    exact hc
  exact hs (stagePoint S H cco normalized F a) (stagePoint S H cco normalized F b) projected

theorem stage_packet_invariant (D : Direction S)
    (β : OrbitalAut G (Quotient (factorCore S H cco D).val)
      (Subtype.val : stageCarriers S H cco normalized F D → _))
    (x y : stageCarriers S H cco normalized F D)
    (hxy : stageFactorPacket S H cco normalized F D x y) :
    stageFactorPacket S H cco normalized F D (β.val x) (β.val y) :=
  (induced_packet_iff (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (stageCarriers S H cco normalized F D) β x y).mpr hxy

theorem stage_target_packet_closed (finiteA : A0.Finite) (D : Direction S)
    (a : StageTuple S H cco normalized F) (ha : a ∈ stageTupleInput S H cco normalized F)
    (y : stageCarriers S H cco normalized F D)
    (hxy : stageFactorPacket S H cco normalized F D (a.val D) y) :
    y ∈ stageFactorTarget S H cco normalized F D := by
  classical
  let finiteInput : (factorInput S H cco A0 D).Finite := finiteA.image _
  let input := finiteInput.toFinset
  have hx : (a.val D).val ∈ factorInput S H cco A0 D :=
    ⟨stagePoint S H cco normalized F a, ha, stagePoint_coordinate S H cco normalized F a D⟩
  have hxa : (a.val D).val ∈ Acl G input :=
    parameter_mem_acl input (finiteInput.mem_toFinset.mpr hx)
  have hya := acl_packet_saturated (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D) input hxa hxy
  change y.val ∈ FiniteLift.aclSet G (↑input : Set _) at hya
  change y.val ∈ FiniteLift.aclSet G (factorInput S H cco A0 D)
  simpa only [input, Set.Finite.coe_toFinset] using hya

/-- The actual closed-safe source theorem supplies one exceptional
factor. Every other WHOLE projected clique lies in the selected packet. -/
theorem stage_exceptional_factor (many : 2 ≤ directionCount S)
    (amalgamate : FiniteLift.StrongClosedAmalgamation G (FiniteLift.aclSet G) (S.menuRel safe))
    (Z : Set (StageTuple S H cco normalized F))
    (hZ : FiniteLift.Unsafe (fun x y => S.menuRel safe
      (stagePoint S H cco normalized F x) (stagePoint S H cco normalized F y)) Z) :
    ∃ D₀ : Direction S, ∀ D : Direction S, D ≠ D₀ → ∀ z ∈ Z, ∀ x ∈ Z,
      stageFactorPacket S H cco normalized F D (z.val D) (x.val D) := by
  obtain ⟨D₀, hD⟩ := unsafe_clique_maximal_packets S H (semanticCCO_change_universe S cco)
    normalized many safe (finset_strong_closed S H safe amalgamate)
    (stagePoint S H cco normalized F '' Z) (stage_original_unsafe S H cco normalized F Z hZ)
  refine ⟨D₀, ?_⟩
  intro D ne z hz x hx
  have h := hD D ne (stagePoint S H cco normalized F z) ⟨z, hz, rfl⟩
    (stagePoint S H cco normalized F x) ⟨x, hx, rfl⟩
  rw [hat_quotient_finite_bottom S H (semanticCCO_change_universe S cco) normalized D] at h
  change finitePacket (factorSource S H (semanticCCO_change_universe S cco) D)
    (factorH S H (semanticCCO_change_universe S cco) D)
    (Quotient.mk'' (stagePoint S H cco normalized F z))
    (Quotient.mk'' (stagePoint S H cco normalized F x)) at h
  rw [stagePoint_coordinate S H cco normalized F z D,
    stagePoint_coordinate S H cco normalized F x D] at h
  exact h

end
end CCO.RankInduction.Factors
