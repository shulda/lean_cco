import CCO.OwnerTransversal.InflationBasic
import CCO.OwnerTransversal.PacketLanguage

/-! Finite ACTUAL full inflations realize in N_B. Repeated U origins
are recognized by literal equality, so all phases of one packet use the
SAME old real origin. All t_g and every fine pair are retained. -/
universe v w t
open scoped FirstOrder
open FirstOrder FirstOrder.Language
namespace CCO.OwnerTransversal.Inflation
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization CountableColour TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

abbrev Signature := PacketLanguage.language (ResidualData.PacketGroup S H) ↥B (FullColour S)

@[instance_reducible] def sourceStructure : (Signature S H R B).Structure (NamedCarrier S H R B) := by
  letI := packetNamedAction S H R B hB
  exact PacketLanguage.ofTable (namedTable S H R B)

@[instance_reducible] def inflationStructure : (Signature S H R B).Structure (Carrier S H R B) := by
  letI := action S H R B
  exact PacketLanguage.ofTable (table S H R B hB)

end
end CCO.OwnerTransversal.Inflation
