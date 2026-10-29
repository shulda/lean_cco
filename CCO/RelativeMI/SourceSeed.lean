import CCO.RelativeMI.CompatibleGroup
import CCO.HKNReservoir.SourcePacketRecovery

/-! Literal realization of the original full packet seed and the finite
universe lift used by the HKN encoder. These conversions add no closure,
safety, fine-owner support or request premise to the principal result. -/
universe v w t
namespace CCO.RelativeMI
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge HKNReservoir
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (U : Finset (Owner S H R)) (hU : PacketInvariant S H R U)
variable (A0 : Finset M)
local notation "N" => NamedCarrier S H R U

def sourceSeed : Finset N :=
  ((packetClosure_finite S H A0).preimage Subtype.val_injective.injOn).toFinset

@[simp] theorem mem_sourceSeed (x : N) :
    x ∈ sourceSeed S H R U A0 ↔ x.val ∈ RealClosure.Bounds.packetClosure S H A0 :=
  Set.Finite.mem_toFinset _

theorem sourceSeed_closed : PacketClosed S H R U (sourceSeed S H R U A0) := by
  intro x hx y hxy
  obtain ⟨a,ha,hax⟩ := (mem_sourceSeed S H R U A0 x).mp hx
  exact (mem_sourceSeed S H R U A0 y).mpr ⟨a,ha,(finitePacket S H).val.trans hax hxy⟩

theorem sourceSeed_real
    (hcontains : ∀ x ∈ RealClosure.Bounds.packetClosure S H A0, owner S H R x ∈ U) :
    Subtype.val '' (↑(sourceSeed S H R U A0) : Set N) =
      RealClosure.Bounds.packetClosure S H A0 := by
  ext x
  constructor
  · rintro ⟨a,ha,rfl⟩
    exact (mem_sourceSeed S H R U A0 a).mp ha
  · intro hx
    let a : N := ⟨x,hcontains x hx⟩
    exact ⟨a,(mem_sourceSeed S H R U A0 a).mpr hx,rfl⟩

def liftedSource (C : Finset N) : Set (SourceCarrier S H R U) := {x | x.down ∈ C}

theorem liftedSource_finite (C : Finset N) : (liftedSource S H R U C).Finite :=
  C.finite_toSet.preimage ULift.down_injective.injOn

theorem liftedSource_closed (C : Finset N) (hC : PacketClosed S H R U C) :
    (sourceStructure S H R U hU).IsClosed (liftedSource S H R U C) := by
  apply (isClosed_encode_iff (sourceData S H R U hU) _).mpr
  intro k x hx
  exact hC x.down hx (packetPoint S H R U hU k x.down)
    (translation_in_packet S (finitePacket S H) G k x.down.val)

theorem liftedSource_support (C : Finset N)
    (hC : ∀ u : ↥U, ∃ a ∈ C, ownerLabel S H R U a = u) :
    ∀ u : ↥U, ∃ a : liftedSource S H R U C, (sourceData S H R U hU).owner a.val = u := by
  intro u
  obtain ⟨a,ha,ho⟩ := hC u
  exact ⟨⟨ULift.up a,ha⟩,ho⟩

theorem liftedSource_contains (C : Finset N) (hC : sourceSeed S H R U A0 ⊆ C)
    (hcontains : ∀ x ∈ RealClosure.Bounds.packetClosure S H A0, owner S H R x ∈ U) :
    ∀ x ∈ RealClosure.Bounds.packetClosure S H A0,
      ∃ a : liftedSource S H R U C, a.val.down.val = x := by
  intro x hx
  let a : N := ⟨x,hcontains x hx⟩
  exact ⟨⟨ULift.up a,hC ((mem_sourceSeed S H R U A0 a).mpr hx)⟩,rfl⟩

theorem liftedSource_nonempty (C : Finset N) (hC : sourceSeed S H R U A0 ⊆ C)
    (hcontains : ∀ x ∈ RealClosure.Bounds.packetClosure S H A0, owner S H R x ∈ U)
    (hne : A0.Nonempty) : (liftedSource S H R U C).Nonempty := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨a,_⟩ := liftedSource_contains S H R U A0 C hC hcontains x
    ⟨x,hx,(finitePacket S H).val.refl _⟩
  exact ⟨a.val,a.property⟩

theorem liftedSource_safe_cross (C : Finset N) (safe : Set (S.Atom () ()))
    (hSafe : ∀ a ∈ C, a ∉ sourceSeed S H R U A0 → ∀ b ∈ C,
      ¬ finitePacket S H a.val b.val → ∃ d ∈ safe, col S a.val b.val = some d) :
    ∀ a : liftedSource S H R U C,
      a.val.down.val ∉ RealClosure.Bounds.packetClosure S H A0 →
      ∀ b : liftedSource S H R U C,
        ¬ finitePacket S H a.val.down.val b.val.down.val →
          ∃ d ∈ safe, col S a.val.down.val b.val.down.val = some d := by
  intro a ha b hab
  exact hSafe a.val.down a.property
    (fun hm => ha ((mem_sourceSeed S H R U A0 a.val.down).mp hm)) b.val.down b.property hab

end
end CCO.RelativeMI
