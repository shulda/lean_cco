import CCO.RelativeMI.SafeSelector
import CCO.RelativeMI.UniversalLifts

/-! ONE fixed PC family on ALL actual full-row packets. An independent
safe certificate proves survivors on every original hole; it is not made
equivariant. All parameters and endpoint translations remain independent. -/
universe v w t y
namespace CCO.RelativeMI
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings Selectors FullRows
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
variable (safe : Set (S.Atom () ()))
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "J" => Packet I K
local notation "T" => TransversalSource.source S H R B
local notation "D₀" => rowDiagram S H R B hB Δ A hA E hLocal
local notation "P₀" => sourceOriginPattern S H R B hB Δ A hA E hLocal
local notation "SG" => orbitSafe S H R B hB safe

theorem rowDiagram_hole (p q : J) (hpq : p ≠ q)
    (hhole : (P₀).edge p.1 q.1 = none) : (D₀).edge p q hpq = none := by
  cases he : (D₀).edge p q hpq with
  | none => rfl
  | some a =>
    have hh := (rowDiagram_edge S H R B hB Δ A hA E hLocal p q hpq a).mp he
    rw [hhole] at hh
    cases hh

include c in
/-- A single same-vertex safe completion supplies survivors in the SAME
greatest original PC family, even for equal structural indices. -/
theorem rowFixed_hole_meets_orbitSafe (hs : SafeSystem T SG)
    (p : DistinctPair J) (hhole : (P₀).edge p.src.1 p.dst.1 = none) :
    (rowFixedMenu S H R B hB Δ A hA E hLocal p ∩
      SG ((D₀).vertexSort p.src) ((D₀).vertexSort p.dst)).Nonempty := by
  obtain ⟨f,hf⟩ := rowDiagram_strongCompletion S H R B hB Δ A hA E hLocal c
  obtain ⟨g,hg,hgsafe⟩ := safe_certificate T hs D₀ f hf
  obtain ⟨a,ha,hcol⟩ := hgsafe p.src p.dst p.ne
    (rowDiagram_hole S H R B hB Δ A hA E hLocal p.src p.dst p.ne hhole)
  exact ⟨a,StrongPC.fixedNetwork_supports_completion D₀ g hg p a hcol,ha⟩

include c in
/-- Both endpoint types move separately; rows and phases are arbitrary. -/
theorem vertexDomain_hole_meets_orbitSafe (hs : SafeSystem T SG)
    (x y : Vertex I K) (hxy : x.1 ≠ y.1)
    (hhole : (P₀).edge x.1.1 y.1.1 = none) :
    (vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy ∩
      SG (vertexOwner S H R B hB Δ A hA E hLocal x)
        (vertexOwner S H R B hB Δ A hA E hLocal y)).Nonempty := by
  letI := TransversalPure.thinCommGroup S H R
  let Q := TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  obtain ⟨a,ha,hsafe⟩ := rowFixed_hole_meets_orbitSafe S H R B hB Δ A hA E hLocal c safe hs
    ⟨x.1,y.1,hxy⟩ hhole
  refine ⟨gaugeAtom Q x.2 y.2 _ _ a,⟨a,ha,rfl⟩,?_⟩
  exact (orbitSafe_left_iff S H R B hB safe x.2 _).mpr
    ((orbitSafe_right_iff S H R B hB safe y.2 a).mpr hsafe)

/-- C13/C16: u, the two endpoint phases, and both further matrix shifts
are entirely independent. Every final value is in ORIGINAL raw safe. -/
theorem vertexReading_full_matrix_safe (hs : SafeSystem T SG)
    (hq : readingData.SafeOn S H R B hB Δ SG)
    (x y : Vertex I K) (hxy : x.1 ≠ y.1)
    (hhole : (P₀).edge x.1.1 y.1.1 = none) (u g k : K) :
    ∃ a ∈ safe, switchColour S (finitePacket S H) (g*k)
      (some (parametricReading S H R B hB Δ readingData hΔ u
        (vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy)
        (vertexDomain_exact S H R B hB Δ hΔ A hA E hLocal c x y hxy)).val) = some a := by
  have hm := vertexDomain_hole_meets_orbitSafe S H R B hB Δ hΔ A hA E hLocal c safe hs x y hxy hhole
  have hr := parametricReading_orbitSafe S H R B hB Δ readingData hΔ safe hq u _
    (vertexDomain_exact S H R B hB Δ hΔ A hA E hLocal c x y hxy) hm
  exact (orbitSafe_matrix_iff S H R B hB safe _).mp hr g k

theorem decodedColour_hole_safe (hs : SafeSystem T SG)
    (hq : readingData.SafeOn S H R B hB Δ SG)
    (x y : Vertex I K) (hxy : x.1 ≠ y.1)
    (hhole : (P₀).edge x.1.1 y.1.1 = none) :
    ∃ a ∈ safe, decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y = some a := by
  letI := TransversalPure.thinCommGroup S H R
  have hm := vertexDomain_hole_meets_orbitSafe S H R B hB Δ hΔ A hA E hLocal c safe hs x y hxy hhole
  have hr := parametricReading_orbitSafe S H R B hB Δ readingData hΔ safe hq (parameter x y) _
    (vertexDomain_exact S H R B hB Δ hΔ A hA E hLocal c x y hxy) hm
  exact ⟨_,orbitSafe_subset S H R B hB safe hr,
    decodedColour_eq_reading S H R B hB Δ readingData hΔ A hA E hLocal c x y hxy⟩

theorem decodedColour_hole_matrix_safe (hs : SafeSystem T SG)
    (hq : readingData.SafeOn S H R B hB Δ SG)
    (x y : Vertex I K) (hxy : x.1 ≠ y.1)
    (hhole : (P₀).edge x.1.1 y.1.1 = none) (g k : K) :
    letI := TransversalPure.thinCommGroup S H R
    ∃ a ∈ safe,
      decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c
        (translate g x) (translate k y) = some a := by
  letI := TransversalPure.thinCommGroup S H R
  exact decodedColour_hole_safe S H R B hB Δ readingData hΔ A hA E hLocal c safe hs hq
    (translate g x) (translate k y) hxy hhole

end
end CCO.RelativeMI
