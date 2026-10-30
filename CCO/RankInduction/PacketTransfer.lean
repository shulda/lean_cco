import CCO.RankInduction.OrbitalEquivalence
import CCO.Owners.Master.PacketCongruence

/-! Actual greatest finite packets are intrinsic to the original group
action. Equivariant carrier identifications and different complete orbital
names do not introduce a new packet or an atom-coding compatibility premise. -/

universe v w q r t
namespace CCO.RankInduction.Factors
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open Owners.Provider Owners.Master

variable {M : Type v} {N : Type q} {G : Type t}
variable [Group G] [MulAction G M] [MulAction G N]
variable (S : AtomicSource.{0,v,w} Unit (fun _ => M)) (HS : HomogeneousSource S G)
variable (T : AtomicSource.{0,q,r} Unit (fun _ => N)) (HT : HomogeneousSource T G)
variable (e : M ≃ N) (equivariant : ∀ (g : G) x, e (g • x) = g • e x)

/-- Pull back the actual target packet as an original invariant
equivalence; no equality between the two atomic palettes is needed. -/
def packetPullback : ColourEq S () := by
  refine ⟨Setoid.comap e (finitePacket T HT).val, ?_⟩
  apply groupInvariant_colourInvariant S HS
  intro g x y hxy
  change finitePacket T HT (e (g • x)) (e (g • y))
  rw [equivariant, equivariant]
  exact colourInvariant_groupInvariant T HT (finitePacket T HT).property g (e x) (e y) hxy

/-- Each pulled-back class injects into one ACTUAL finite target packet. -/
theorem packetPullback_finite : FiniteClasses S (packetPullback S HS T HT e equivariant) := by
  intro x
  let := finitePacket_finite T HT (e x)
  let f : ClassPoint S () (packetPullback S HS T HT e equivariant) x →
      ClassPoint T () (finitePacket T HT) (e x) := fun y => ⟨e y.val, y.property⟩
  exact Finite.of_injective f (fun _ _ h =>
    Subtype.ext (e.injective (congrArg Subtype.val h)))

theorem packetPullback_le : packetPullback S HS T HT e equivariant ≤ finitePacket S HS :=
  le_finitePacket S HS _ (packetPullback_finite S HS T HT e equivariant)

include equivariant in
/-- Finite packets transport in BOTH directions under the displayed
equivariant ambient equivalence, including the entire original action. -/
theorem packet_equiv (x y : M) :
    finitePacket S HS x y ↔ finitePacket T HT (e x) (e y) := by
  constructor
  · intro hxy
    have old : packetPullback T HT S HS e.symm (equivariant_symm e equivariant)
        (e x) (e y) := by
      change finitePacket S HS (e.symm (e x)) (e.symm (e y))
      simpa only [Equiv.symm_apply_apply] using hxy
    exact (packetPullback_le T HT S HS e.symm (equivariant_symm e equivariant)) old
  · intro hxy
    have pulled : packetPullback S HS T HT e equivariant x y := hxy
    exact (packetPullback_le S HS T HT e equivariant) pulled

include equivariant in
/-- Full finite-packet closure transports as a statement about the SAME
literal image subset, rather than newly selected representatives. -/
theorem packet_closed_image (D : Set M)
    (closed : ∀ x ∈ D, ∀ y, finitePacket S HS x y → y ∈ D) :
    ∀ x ∈ e '' D, ∀ y, finitePacket T HT x y → y ∈ e '' D := by
  rintro x ⟨a, ha, rfl⟩ y hxy
  refine ⟨e.symm y, closed a ha (e.symm y) ?_, e.apply_symm_apply y⟩
  apply (packet_equiv S HS T HT e equivariant a (e.symm y)).mpr
  simpa only [Equiv.apply_symm_apply] using hxy

/-- The owner source and any actual homogeneous source on the SAME
owner carrier have identical finite-packet setoids. This uses only their
common original pair action, not a surjection of full automorphism groups. -/
theorem owner_packet_eq (π : M → N) (onto : Function.Surjective π)
    (equivariantπ : ∀ (g : G) x, π (g • x) = g • π x) :
    (ownerPacket S HS π onto equivariantπ).val = (finitePacket T HT).val := by
  let P := pairAction_of_homogeneous T HT
  have equality := packet_eq_of_pairActions T (ownerSource S HS π onto equivariantπ)
    P (ownerPairAction S HS π onto equivariantπ)
  rw [P.packet_eq_accepted HT] at equality
  exact equality.symm

theorem owner_packet_iff (π : M → N) (onto : Function.Surjective π)
    (equivariantπ : ∀ (g : G) x, π (g • x) = g • π x) (x y : N) :
    ownerPacket S HS π onto equivariantπ x y ↔ finitePacket T HT x y := by
  rw [owner_packet_eq S HS T HT π onto equivariantπ]

end
end CCO.RankInduction.Factors
