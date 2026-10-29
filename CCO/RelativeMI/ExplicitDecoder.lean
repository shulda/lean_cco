import CCO.RelativeMI.DecodedAge
import CCO.FullRows.ReadingMatrix

/-! The inflated literal matrix is exactly the source's vertex-by-vertex
moving-reading formula, for ALL distinct ACTUAL packets. -/
universe v w t y
namespace CCO.RelativeMI
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
open SafeReadings Selectors FullRows
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (readingData : JointReading S H R B hB Δ)
variable (hΔ : ∀ g, TransversalPure.diagonal S H R B hB g ∈ Δ)
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
variable (c : PacketCertificate S H R B hB Δ A hA E hLocal)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "J" => Packet I K
local notation "U₀" => TransversalSource.source S H R B

theorem decodedColour_eq_reading (x y : Vertex I K) (hxy : x.1 ≠ y.1) :
    letI := TransversalPure.thinCommGroup S H R
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y =
      some (parametricReading S H R B hB Δ readingData hΔ (parameter x y)
        (vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy)
        (vertexDomain_exact S H R B hB Δ hΔ A hA E hLocal c x y hxy)).val := by
  classical
  letI := TransversalPure.thinCommGroup S H R
  let Q := TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  let h := readingData.selector
  let M₀ := rowFixedMenu S H R B hB Δ A hA E hLocal ⟨x.1,y.1,hxy⟩
  let u := parameter (x.1,1) (y.1,1)
  have hu : parameter x y = u*x.2*y.2 := parameter_phases x y
  have hh := reading_matrix_label Q h (readingData.covariant)
    u x.2 y.2 M₀ (rowFixed_exact S H R B hB Δ A hA E hLocal c ⟨x.1,y.1,hxy⟩)
    (vertexDomain_exact S H R B hB Δ hΔ A hA E hLocal c x y hxy)
  change (some (parametricReading S H R B hB Δ readingData hΔ (u*x.2*y.2)
      (vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy)
      (vertexDomain_exact S H R B hB Δ hΔ A hA E hLocal c x y hxy)).val : FullColour S) =
    switchColour S (finitePacket S H) (x.2*y.2)
      (some (originAtom S H R B hB Δ readingData hΔ A hA E hLocal c ⟨x.1,y.1,hxy⟩).val) at hh
  change (if h : x.1 = y.1 then _ else _) = _
  rw [dif_neg hxy,hu]
  exact hh.symm

theorem decodedColour_symmetric (x y : Vertex I K) :
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y =
      decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c y x :=
  (decodedPoint_colour S H R B hB Δ readingData hΔ A hA E hLocal c x y).symm.trans
    ((col_symm S _ _).trans (decodedPoint_colour S H R B hB Δ readingData hΔ A hA E hLocal c y x))

theorem decodedColour_none (x y : Vertex I K) :
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y = none ↔ x = y := by
  rw [← decodedPoint_colour S H R B hB Δ readingData hΔ A hA E hLocal c x y,col_none]
  exact ⟨fun he => decodedPoint_injective S H R B hB Δ readingData hΔ A hA E hLocal c (Subtype.ext he),
    fun he => congrArg (fun z => (decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c z).val) he⟩

/-- ALL triangles, including one/two-packet cases, are actual original
source triangles because the literal full matrix has a genuine embedding. -/
theorem decoded_triangle (x y z : Vertex I K) (a b d : S.Atom () ())
    (hxy : decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y = some a)
    (hyz : decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c y z = some b)
    (hxz : decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x z = some d) : S.Triangle a b d :=
  ⟨(decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c x).val,
    (decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c y).val,
    (decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c z).val,
    (decodedPoint_colour S H R B hB Δ readingData hΔ A hA E hLocal c x y).trans hxy,
    (decodedPoint_colour S H R B hB Δ readingData hΔ A hA E hLocal c y z).trans hyz,
    (decodedPoint_colour S H R B hB Δ readingData hΔ A hA E hLocal c x z).trans hxz⟩
end
end CCO.RelativeMI
