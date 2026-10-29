import CCO.OwnerTransversal.TransversalInstance
import CCO.OwnerTransversal.PacketAction
import CCO.OwnerTransversal.PacketCoordinates

/-! The ACTUAL full-packet inflation of the internally constructed U.
Owner actions can have nontrivial stabilizers. All fine colours, including
within-packet equality, use the accepted two-endpoint transport law. -/
universe v w t
namespace CCO.OwnerTransversal.Inflation
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization CountableColour TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R))

abbrev Carrier := U S H R B × ResidualData.PacketGroup S H

@[instance_reducible] def action : MulAction (ResidualData.PacketGroup S H) (Carrier S H R B) where
  smul e x := (x.1,e * x.2)
  one_smul x := Prod.ext rfl (one_mul x.2)
  mul_smul e f x := Prod.ext rfl (mul_assoc e f x.2)

def table (hB : PacketInvariant S H R B) : Table ↥B (FullColour S) (Carrier S H R B) := by
  letI := packetOwnerSetAction S H R B hB
  exact ⟨fun x => x.2 • (limitTable S H R B).owner x.1,
    fun x y => switchColour S (finitePacket S H) (x.2 * y.2)
      ((limitTable S H R B).colour x.1 y.1)⟩

def namedTable : Table ↥B (FullColour S) (NamedCarrier S H R B) :=
  ⟨ownerLabel S H R B,fun x y => col S x.val y.val⟩

@[simp] theorem table_owner_one (hB : PacketInvariant S H R B) (u : U S H R B) :
    (table S H R B hB).owner (u,1) = (limitTable S H R B).owner u := by
  letI := packetOwnerSetAction S H R B hB
  exact one_smul _ _

@[simp] theorem table_colour_one (hB : PacketInvariant S H R B) (u v : U S H R B) :
    (table S H R B hB).colour (u,1) (v,1) = (limitTable S H R B).colour u v := by
  simp only [table,one_mul,switchColour_one]

/-- Every finite origin realization transports the ENTIRE fine matrix,
including repeated origins and equality, to its whole packet inflation. -/
theorem realized_matrix {I : Type*} (u : I → U S H R B)
    (p : I → NamedCarrier S H R B)
    (hp : ∀ i j, col S (p i).val (p j).val = (limitTable S H R B).colour (u i) (u j))
    (hB : PacketInvariant S H R B) (i j : I)
    (g h : ResidualData.PacketGroup S H) :
    col S (g.val (p i).val) (h.val (p j).val) =
      (table S H R B hB).colour (u i,g) (u j,h) := by
  rw [two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H),hp]
  rfl

/-- The original real packet action is regular, independently of its
possibly nonfaithful action on owners. -/
theorem named_action_free (hB : PacketInvariant S H R B) (x : NamedCarrier S H R B) :
    Function.Injective (fun g : ResidualData.PacketGroup S H => packetPoint S H R B hB g x) := by
  intro g h he
  apply translationColour_injective S (finitePacket S H) H (R.packet_thin S H)
  exact (translationColour_at S (finitePacket S H) H g x.val).symm.trans
    ((congrArg (fun y : NamedCarrier S H R B => col S x.val y.val) he).trans
      (translationColour_at S (finitePacket S H) H h x.val))

/-- Coordinate packets carry the regular left action without an owner
faithfulness premise. -/
theorem action_free (x : Carrier S H R B) :
    Function.Injective (fun g => (action S H R B).smul g x) := by
  intro g h he
  exact mul_right_cancel (congrArg Prod.snd he)

end
end CCO.OwnerTransversal.Inflation
