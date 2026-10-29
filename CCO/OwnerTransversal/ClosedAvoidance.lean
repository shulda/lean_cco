import CCO.OwnerTransversal.NamedSource

/-! Finite avoidance in the actual full named-owner automorphism group.
Only finite PACKET-closed bases are used; original real-age SAP is absent. -/

universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds AclOwners
open FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

def PacketClosed (C : Finset (NamedCarrier S H R B)) : Prop :=
  ∀ x ∈ C, ∀ y : NamedCarrier S H R B, finitePacket S H x.val y.val → y ∈ C

def baseFixers (C : Finset (NamedCarrier S H R B)) : Subgroup (NamedAut S H R B) where
  carrier := {f | ∀ c ∈ C, f.val c = c}
  one_mem' := fun _ _ => rfl
  mul_mem' := by
    intro f g hf hg c hc
    change f.val (g.val c) = c
    rw [hg c hc,hf c hc]
  inv_mem' := by
    intro f hf c hc
    apply f.val.injective
    change f.val (f.val.symm c) = f.val c
    rw [Equiv.apply_symm_apply,hf c hc]

theorem packetClosed_iff_closure (C : Finset (NamedCarrier S H R B)) :
    PacketClosed S H R B C ↔ namedPacketClosure S H R B C ⊆ (C : Set _) := by
  constructor
  · rintro h y ⟨a,ha,hay⟩
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
    exact h x hx y hay
  · intro h x hx y hxy
    exact h ⟨x.val,(mem_realBase S H R B C x).mpr hx,hxy⟩

theorem subset_namedPacketFinset (A : Finset (NamedCarrier S H R B)) :
    A ⊆ namedPacketFinset S H R B A := by
  intro a ha
  exact (mem_namedPacketFinset S H R B A a).mpr
    ⟨a.val,(mem_realBase S H R B A a).mpr ha,(finitePacket S H).val.refl _⟩

theorem packetClosed_namedPacketFinset (A : Finset (NamedCarrier S H R B)) :
    PacketClosed S H R B (namedPacketFinset S H R B A) := by
  intro x hx y hxy
  obtain ⟨a,ha,hax⟩ := (mem_namedPacketFinset S H R B A x).mp hx
  exact (mem_namedPacketFinset S H R B A y).mpr
    ⟨a,ha,(finitePacket S H).val.trans hax hxy⟩

theorem fixed_orbit_eq (C : Finset (NamedCarrier S H R B))
    (x : NamedCarrier S H R B) :
    MulAction.orbit (baseFixers S H R B C) x =
      orbitOver (NamedAut S H R B) C x := by
  ext y
  constructor
  · rintro ⟨f,rfl⟩
    exact ⟨f.val,f.property,rfl⟩
  · rintro ⟨f,hf,rfl⟩
    exact ⟨⟨f,hf⟩,rfl⟩

variable [Infinite M]

/-- C25: one automorphism moves the WHOLE off-base finite request away
from the finite forbidden set, while retaining every point of C. -/
theorem finite_closed_avoidance (C A Z : Finset (NamedCarrier S H R B))
    (hC : PacketClosed S H R B C) :
    ∃ f : NamedAut S H R B, (∀ c ∈ C, f.val c = c) ∧
      ∀ a ∈ A, a ∉ C → ∀ z ∈ Z, f.val a ≠ z := by
  classical
  let K := baseFixers S H R B C
  have hinf : ∀ x ∈ A \ C, (MulAction.orbit K x).Infinite := by
    intro x hx
    rw [fixed_orbit_eq S H R B]
    apply named_orbit_infinite S H R B C x
    intro hxcl
    exact (Finset.mem_sdiff.mp hx).2 ((packetClosed_iff_closure S H R B C).mp hC hxcl)
  obtain ⟨f,hf⟩ := finite_action_avoidance (G := K) (A \ C) Z hinf
  refine ⟨f.val,f.property,?_⟩
  intro a ha hna z hz
  exact hf a (Finset.mem_sdiff.mpr ⟨ha,hna⟩) z hz

/-- The induced-copy form allows arbitrary old overlaps; no off-base
point is required to remain fixed. -/
theorem closed_disjoint_copy (C A L : Finset (NamedCarrier S H R B))
    (hC : PacketClosed S H R B C) :
    ∃ f : NamedAut S H R B, (∀ c ∈ C, f.val c = c) ∧
      ∀ a ∈ A, ∀ l ∈ L, f.val a = l → l ∈ C := by
  obtain ⟨f,hfix,havoid⟩ := finite_closed_avoidance S H R B C A L hC
  refine ⟨f,hfix,?_⟩
  intro a ha l hl he
  by_cases hac : a ∈ C
  · exact ((hfix a hac).symm.trans he) ▸ hac
  · exact False.elim (havoid a ha hac l hl he)

/-- Packet-closed finite induced sets are preserved by every named
automorphism; this uses the full original colour table. -/
theorem packetClosed_image (A : Finset (NamedCarrier S H R B))
    (hA : PacketClosed S H R B A) (f : NamedAut S H R B) :
    PacketClosed S H R B (A.image f.val) := by
  classical
  rintro x hx y hxy
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  have hcol := NamedAut.colour_fixed f a (f.val.symm y)
  rw [Equiv.apply_symm_apply] at hcol
  have hF : finitePacket S H a.val (f.val.symm y).val :=
    ((finitePacket S H).property a.val (f.val.symm y).val (f.val a).val y.val hcol.symm).mpr hxy
  exact Finset.mem_image.mpr ⟨f.val.symm y,hA a ha (f.val.symm y) hF,Equiv.apply_symm_apply _ _⟩

theorem packetClosed_union (A L : Finset (NamedCarrier S H R B))
    (hA : PacketClosed S H R B A) (hL : PacketClosed S H R B L) :
    PacketClosed S H R B (A ∪ L) := by
  intro x hx y hxy
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (hA x hx y hxy)
  · exact Finset.mem_union_right _ (hL x hx y hxy)

end
end CCO.OwnerTransversal
