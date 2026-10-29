import CCO.OwnerTransversal.PacketImages

/-! Actual packet translations act on original E-owners and on the whole
named preimage of a packet-invariant owner set. Only the real packet action
is regular; these owner actions are not assumed faithful or free. -/

universe v w t
namespace CCO.OwnerTransversal
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)

def packetOwnerMove (e : ResidualData.PacketGroup S H) : Owner S H R → Owner S H R :=
  Quotient.map e.val (by
    intro x y hxy
    exact (R.E.property x y (e.val x) (e.val y)
      (translation_preserves_colour S (finitePacket S H) H (R.packet_thin S H) e x y).symm).mp hxy)

@[simp] theorem packetOwnerMove_owner (e : ResidualData.PacketGroup S H) (x : M) :
    packetOwnerMove S H R e (owner S H R x) = owner S H R (e.val x) := rfl

@[simp] theorem packetOwnerMove_one (q : Owner S H R) :
    packetOwnerMove S H R 1 q = q := Quotient.inductionOn q (fun _ => rfl)

theorem packetOwnerMove_mul (e f : ResidualData.PacketGroup S H) (q : Owner S H R) :
    packetOwnerMove S H R (e * f) q =
      packetOwnerMove S H R e (packetOwnerMove S H R f q) :=
  Quotient.inductionOn q (fun _ => rfl)

@[instance_reducible] def packetOwnerAction : MulAction (ResidualData.PacketGroup S H) (Owner S H R) where
  smul := packetOwnerMove S H R
  one_smul := packetOwnerMove_one S H R
  mul_smul := packetOwnerMove_mul S H R

theorem packetOwnerMove_mem (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
    (e : ResidualData.PacketGroup S H) (q : Owner S H R) (hq : q ∈ B) :
    packetOwnerMove S H R e q ∈ B := by
  induction q using Quotient.inductionOn with
  | _ x => exact hB e x hq

@[instance_reducible] def packetNamedAction (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B) :
    MulAction (ResidualData.PacketGroup S H) (NamedCarrier S H R B) where
  smul := packetPoint S H R B hB
  one_smul := packetPoint_one S H R B hB
  mul_smul := packetPoint_mul S H R B hB

@[instance_reducible] def packetOwnerSetAction (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B) :
    MulAction (ResidualData.PacketGroup S H) ↥B where
  smul e q := ⟨packetOwnerMove S H R e q.val,packetOwnerMove_mem S H R B hB e q.val q.property⟩
  one_smul q := Subtype.ext (packetOwnerMove_one S H R q.val)
  mul_smul e f q := Subtype.ext (packetOwnerMove_mul S H R e f q.val)

theorem named_owner_equivariant (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
    (e : ResidualData.PacketGroup S H) (x : NamedCarrier S H R B) :
    (⟨owner S H R (packetPoint S H R B hB e x).val,
      (packetPoint S H R B hB e x).property⟩ : ↥B) =
      (packetOwnerSetAction S H R B hB).smul e ⟨owner S H R x.val,x.property⟩ := rfl

/-- The kernel is the full actual owner stabilizer, with no faithfulness
assertion on this quotient action. -/
theorem packetOwnerMove_fixed_iff (e : ResidualData.PacketGroup S H) :
    (∀ q : Owner S H R, packetOwnerMove S H R e q = q) ↔
      e ∈ ResidualData.ownerStabilizer S H R := by
  constructor
  · intro he x
    exact (R.E.val.symm (Quotient.exact (he (owner S H R x))))
  · intro he q
    induction q using Quotient.inductionOn with
    | _ x => exact Quotient.sound (R.E.val.symm (he x))

end
end CCO.OwnerTransversal
