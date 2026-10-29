import CCO.HKNReservoir.TypedOrigins
import CCO.HKNReservoir.SourcePacketOrigins

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
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)

/-- The WHOLE original partial origin diagram, with literal typed owner
palettes attached; no records or holes are changed by this interpretation. -/
def sourceOriginDiagram : PartialDiagram (SafeReadings.TransversalSource.source S H R B)
    (PacketRecovery.PacketIndex E) :=
  typedOriginDiagram S H R B (sourceOriginPattern S H R B hB Δ A hA E hLocal)
    (sourceOriginOwner S H R B hB Δ A hA E hLocal)
    (sourceOriginPalette S H R B hB Δ A hA E hLocal)

theorem sourceOriginDiagram_edge (i j : PacketRecovery.PacketIndex E) (hij : i ≠ j)
    (a : (SafeReadings.TransversalSource.source S H R B).Atom
      (sourceOriginOwner S H R B hB Δ A hA E hLocal i)
      (sourceOriginOwner S H R B hB Δ A hA E hLocal j)) :
    (sourceOriginDiagram S H R B hB Δ A hA E hLocal).edge i j hij = some a ↔
      E.rel (.fine a.val) (![sourceOrigin S H R B hB Δ A hA E hLocal i,
        sourceOrigin S H R B hB Δ A hA E hLocal j]) :=
  (typedOriginEdge_some S H R B _ _ _ i j a).trans
    (sourceOriginPattern_edge S H R B hB Δ A hA E hLocal i j a.val)

end
end CCO.HKNReservoir
