import CCO.HKNReservoir.SourceOriginDiagram
import CCO.HKNReservoir.Locality.CycleBound
import CCO.SafeReadings.TransversalSAP

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

/-- C27–C28: test EVERY specified simple cycle of the WHOLE diagram.
Short cycles are the local HKN obligation; the proved finite bound handles
all longer cycles. Only this final step uses actual typed semantic CCO. -/
theorem whole_origin_certificate
    (short : ∀ C : SimpleCycle (sourceOriginDiagram S H R B hB Δ A hA E hLocal),
      C.length ≤ Locality.cycleBound (SafeReadings.TransversalSource.source S H R B) → CycleHom C) :
    Nonempty (OriginMap S H R B (sourceOriginPattern S H R B hB Δ A hA E hLocal)) := by
  obtain ⟨f⟩ := Locality.completion_of_short_cycles
    (SafeReadings.TransversalSource.source S H R B)
    (SafeReadings.TransversalSource.canonical_homogeneous S H R B)
    (SafeReadings.TransversalSource.ageSAP S H R B)
    (SafeReadings.TransversalSource.sortwise_primitive S H R B)
    (semanticCCO_change_universe _ (SafeReadings.TransversalSource.semanticCCO S H R B))
    (sourceOriginDiagram S H R B hB Δ A hA E hLocal) short
  exact named_origins_of_typed_hom S H R B _ _ _ (fun _ => rfl) f

end
end CCO.HKNReservoir
