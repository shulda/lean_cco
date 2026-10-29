import CCO.HKNReservoir.SourcePacketOrigins

/-! An existential completion certificate on the SAME structural carrier.
The original structure and its automorphisms remain the reservoir; this
map does not choose an equivariant filling of unrecorded fine holes. -/
universe v w t y
namespace CCO.HKNReservoir
noncomputable section
open AllThoseEPPA ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y}
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)

structure PacketCertificate where
  point : Z → NamedCarrier S H R B
  injective : Function.Injective point
  owner : ∀ x, ownerLabel S H R B (point x) =
    PacketRecovery.owner (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) E hLocal x
  move : ∀ g x, point (PacketRecovery.move (sourceTag S H R B Δ)
    (finiteSourceData S H R B hB A hA) E hLocal g x) = packetPoint S H R B hB g (point x)
  fine : ∀ a x y, E.rel (.fine a) (![x,y]) → col S (point x).val (point y).val = some a

namespace PacketCertificate
variable {S H R B hB Δ A hA E hLocal}

/-- Pull back the actual complete source table to the SAME formal carrier. -/
def completionData (c : PacketCertificate S H R B hB Δ A hA E hLocal) :
    Data ↥B (ResidualData.PacketGroup S H) (S.Atom () ()) Z where
  owner x := ownerLabel S H R B (c.point x)
  fine a x y := col S (c.point x).val (c.point y).val = some a
  move := PacketRecovery.move (sourceTag S H R B Δ) (finiteSourceData S H R B hB A hA) E hLocal

/-- The complete certificate is a genuine exact source embedding, with
literal owners and equality of WHOLE unary function-value sets. -/
def embedding (c : PacketCertificate S H R B hB Δ A hA E hLocal) :
    Structure.Embedding (sourceAction S H R B Δ) (encode c.completionData)
      (sourceStructure S H R B hB) :=
  (ExactMap.mk (tag := sourceTag S H R B Δ) (D := c.completionData)
    (E := sourceData S H R B hB) 1 (fun x => ULift.up (c.point x))
    (fun _ _ h => c.injective (congrArg ULift.down h))
    (fun _ => rfl) (fun _ _ _ => Iff.rfl)
    (fun g x => ULift.ext _ _ (c.move g x))).toEmbedding

theorem fine_complete (c : PacketCertificate S H R B hB Δ A hA E hLocal)
    (x y : Z) (hxy : x ≠ y) : ∃ a, c.completionData.fine a x y := by
  exact source_fine_complete S H R B hB
    (fun he => hxy (c.injective (congrArg ULift.down he)))
end PacketCertificate
end
end CCO.HKNReservoir
