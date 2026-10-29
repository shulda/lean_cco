import CCO.OwnerTransversal.TransversalExtension
import CCO.OwnerTransversal.PacketAction
import CCO.OwnerTransversal.InflationBasic

/-! Actual independent endpoint transport inside U. Only the finite
request is realized; neither an origin section nor a global action on U
is chosen. Distinct original U points stay in different F packets. -/
universe v w t z
namespace CCO.SafeReadings.TransversalGauge
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

/-- The entire independently switched finite matrix has an actual
injective realization on the SAME transversal U and moved owner fibres. -/
theorem switch_tuple {I : Type z} [Finite I] (u : I → U S H R B)
    (hu : Function.Injective u) (e : I → ResidualData.PacketGroup S H) :
    letI := packetOwnerSetAction S H R B hB
    ∃ v : I ↪ U S H R B,
      (∀ i, (limitTable S H R B).owner (v i) = e i • (limitTable S H R B).owner (u i)) ∧
      ∀ i j, (limitTable S H R B).colour (v i) (v j) =
        switchColour S (finitePacket S H) (e i * e j) ((limitTable S H R B).colour (u i) (u j)) := by
  letI := packetOwnerSetAction S H R B hB
  obtain ⟨a,ho,hc,hs⟩ := realize_tuple S H R B u
  let p : I → NamedCarrier S H R B := fun i => packetPoint S H R B hB (e i) (a i)
  have hp : ∀ i j, i ≠ j → ¬ finitePacket S H (p i).val (p j).val := by
    intro i j hij hF
    exact hs i j (fun he => hij (hu he)) ((finitePacket S H).val.trans
      (translation_in_packet S (finitePacket S H) G (e i) (a i).val)
      ((finitePacket S H).val.trans hF
        ((finitePacket S H).val.symm (translation_in_packet S (finitePacket S H) G (e j) (a j).val))))
  obtain ⟨v,hvo,hvc⟩ := embed_origins S H R B p hp
  refine ⟨v,?_,?_⟩
  · intro i
    exact (hvo i).trans ((named_owner_equivariant S H R B hB (e i) (a i)).trans
      (congrArg (fun b => e i • b) (ho i)))
  · intro i j
    rw [hvc]
    exact (two_endpoint_transport S (finitePacket S H) H (R.packet_thin S H) (e i) (e j)
      (a i).val (a j).val).trans (congrArg (switchColour S (finitePacket S H) (e i * e j)) (hc i j))

end
end CCO.SafeReadings.TransversalGauge
