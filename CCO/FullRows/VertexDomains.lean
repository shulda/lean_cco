import CCO.FullRows.RowCertificate
import CCO.FullRows.Rows
import CCO.FullRows.GaugeNatural
import CCO.SafeReadings.TransversalReadings
import CCO.StrongExact.PCExactness

universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
open SafeReadings Selectors
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (hΔ : ∀ g, SafeReadings.TransversalPure.diagonal S H R B hB g ∈ Δ)
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "J" => Packet I K
local notation "U₀" => SafeReadings.TransversalSource.source S H R B
local notation "D" => rowDiagram S H R B hB Δ A hA E hLocal

def rowFixedMenu (p : DistinctPair J) : (U₀).Menu ((D).vertexSort p.src) ((D).vertexSort p.dst) :=
  StrongPC.fixedNetwork D p

theorem rowFixed_exact (c : PacketCertificate S H R B hB Δ A hA E hLocal) (p : DistinctPair J) :
    StrongExact.Exact U₀ (rowFixedMenu S H R B hB Δ A hA E hLocal p) :=
  StrongPC.fixedNetwork_exact_of_strongCompletion D
    (SafeReadings.TransversalSource.canonical_homogeneous S H R B)
    (SafeReadings.TransversalSource.ageSAP S H R B)
    (SafeReadings.TransversalSource.semanticCCO S H R B)
    (rowDiagram_strongCompletion S H R B hB Δ A hA E hLocal c) p

/-- Owners retain both the structural origin label and the actual real phase. -/
def vertexOwner (x : Vertex I K) : ↥B :=
  SafeReadings.TransversalGauge.moveOwner S H R B hB x.2
    (sourceOriginOwner S H R B hB Δ A hA E hLocal x.1.1)

/-- The SAME fixed network is transported at the two real endpoints.
This is a genuine endpoint gauge, not a pure language permutation. -/
def vertexDomain (x y : Vertex I K) (hxy : x.1 ≠ y.1) :
    (U₀).Menu (vertexOwner S H R B hB Δ A hA E hLocal x)
      (vertexOwner S H R B hB Δ A hA E hLocal y) := by
  letI := SafeReadings.TransversalPure.thinCommGroup S H R
  let Q := SafeReadings.TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  exact gaugeMenu Q x.2 y.2 (rowFixedMenu S H R B hB Δ A hA E hLocal ⟨x.1,y.1,hxy⟩)

theorem vertexDomain_exact (c : PacketCertificate S H R B hB Δ A hA E hLocal)
    (x y : Vertex I K) (hxy : x.1 ≠ y.1) :
    StrongExact.Exact U₀ (vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy) := by
  letI := SafeReadings.TransversalPure.thinCommGroup S H R
  let Q := SafeReadings.TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  have he : gaugeMenu Q x.2 y.2 (rowFixedMenu S H R B hB Δ A hA E hLocal ⟨x.1,y.1,hxy⟩) =
      Q.leftMenu x.2 (Q.rightMenu y.2 (rowFixedMenu S H R B hB Δ A hA E hLocal ⟨x.1,y.1,hxy⟩)) := by
    ext a
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨Q.right y.2 a,⟨a,ha,rfl⟩,rfl⟩
    · rintro ⟨a,⟨b,hb,rfl⟩,rfl⟩
      exact ⟨b,hb,rfl⟩
  change StrongExact.Exact U₀ (gaugeMenu Q x.2 y.2 _)
  exact he.symm ▸ Q.left_exact x.2 (Q.right_exact y.2 (rowFixed_exact S H R B hB Δ A hA E hLocal c _))

theorem vertexDomain_converse (x y : Vertex I K) (hxy : x.1 ≠ y.1) :
    vertexDomain S H R B hB Δ hΔ A hA E hLocal y x hxy.symm =
      (U₀).opposite (vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy) := by
  letI := SafeReadings.TransversalPure.thinCommGroup S H R
  let Q := SafeReadings.TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  change gaugeMenu Q y.2 x.2 (StrongPC.fixedNetwork D ⟨y.1,x.1,hxy.symm⟩) =
    (U₀).opposite (gaugeMenu Q x.2 y.2 (StrongPC.fixedNetwork D ⟨x.1,y.1,hxy⟩))
  rw [StrongPC.fixedNetwork_converse D ⟨x.1,y.1,hxy⟩]
  exact gauge_opposite Q (SafeReadings.TransversalPure.subgroup_literalConverse S H R B hB Δ) x.2 y.2 _
end
end CCO.FullRows
