import CCO.FullRows.RowCertificate
import CCO.FullRows.GaugeNatural
import CCO.FullRows.Rows
import CCO.FullRows.StructuralCoordinates

/-! Actual record/hole and greatest-domain covariance under every structural
reservoir automorphism and every row correction. No correction legality or
equivariant completion certificate is used in this argument. -/
universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
open SafeReadings
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)
variable (Δ : Subgroup (SourceGamma S H R B))
variable (hΔ : ∀ g, TransversalPure.diagonal S H R B hB g ∈ Δ)
variable (A : Set (SourceCarrier S H R B))
variable (hA : (sourceStructure S H R B hB).IsClosed A)
variable {Z : Type y} [Finite Z]
variable (E : Structure (Signature ↥B (ResidualData.PacketGroup S H) (S.Atom () ())) Z)
variable (hLocal : LocallyInSource (sourceTag S H R B Δ) (encode (finiteSourceData S H R B hB A hA)) E)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "J" => Packet I K
local notation "tag" => sourceTag S H R B Δ
local notation "act" => sourceAction S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "org" => sourceOrigin S H R B hB Δ A hA E hLocal
local notation "own" => sourceOriginOwner S H R B hB Δ A hA E hLocal
local notation "move" => PacketRecovery.move tag D₀ E hLocal

/-- Offsets are the phases of ACTUAL vertex images, not solutions of an
owner equation (which need not determine them for nonfree owners). -/
def rowStructural (s₀ : Structure.Automorphism act E) : Structural I K := by
  let := TransversalPure.thinCommGroup S H R
  exact structuralOfEquivariant (reservoirCoordinateEquiv S H R B hB Δ A hA E hLocal s₀)
    (reservoirCoordinateEquiv_move S H R B hB Δ A hA E hLocal s₀)

omit [Finite Z] in
theorem rowStructural_coordinates (s₀ : Structure.Automorphism act E) (p : I × K) :
    reservoirCoordinateEquiv S H R B hB Δ A hA E hLocal s₀ p =
      ((rowStructural S H R B hB Δ A hA E hLocal s₀).sigma p.1,
        p.2 * (rowStructural S H R B hB Δ A hA E hLocal s₀).offset p.1) := by
  let := TransversalPure.thinCommGroup S H R
  exact structuralOfEquivariant_apply
    (reservoirCoordinateEquiv S H R B hB Δ A hA E hLocal s₀)
    (reservoirCoordinateEquiv_move S H R B hB Δ A hA E hLocal s₀) p

omit [Finite Z] in
private theorem coordinates_origin (i : I) :
    reservoirCoordinates S H R B hB Δ A hA E hLocal (org i) = (i,1) := by
  apply (reservoirCoordinates S H R B hB Δ A hA E hLocal).symm.injective
  rw [Equiv.symm_apply_apply,reservoirCoordinates_symm,
    PacketRecovery.move_one tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)]

omit [Finite Z] in
theorem rowStructural_origin (s₀ : Structure.Automorphism act E) (i : I) :
    s₀ (org i) = move
      ((rowStructural S H R B hB Δ A hA E hLocal s₀).offset i)
      (org ((rowStructural S H R B hB Δ A hA E hLocal s₀).sigma i)) := by
  let := TransversalPure.thinCommGroup S H R
  let c := reservoirCoordinates S H R B hB Δ A hA E hLocal
  have hc := rowStructural_coordinates S H R B hB Δ A hA E hLocal s₀ (i,1)
  have ho : c.symm (i,1) = org i := by
    rw [reservoirCoordinates_symm,
      PacketRecovery.move_one tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)]
  change c (s₀ (c.symm (i,1))) = _ at hc
  rw [ho] at hc
  apply c.injective
  rw [reservoirCoordinates_move,coordinates_origin]
  simpa only [baseMap,one_mul,mul_one] using hc

omit [Finite Z] in
theorem rowStructural_owner (s₀ : Structure.Automorphism act E) (i : I) :
    own ((rowStructural S H R B hB Δ A hA E hLocal s₀).sigma i) =
      TransversalGauge.ownerHom S H R B hB
        ((rowStructural S H R B hB Δ A hA E hLocal s₀).offset i)
        ((TransversalPure.subgroupRelabelling S H R B hB Δ).owner s₀.lang (own i)) := by
  let := TransversalPure.thinCommGroup S H R
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  let Q := TransversalPure.endpointGauge S H R B hB
  have hh := reservoirAutomorphism_owner S H R B hB Δ A hA E hLocal s₀ (org i)
  rw [rowStructural_origin,recovered_owner_move] at hh
  change Q.owner (s.offset i) (own (s.sigma i)) =
    (TransversalPure.subgroupRelabelling S H R B hB Δ).owner s₀.lang (own i) at hh
  have ht := congrArg (fun b => Q.owner (s.offset i) b) hh
  rw [Q.owner_twice] at ht
  exact ht

def rowPacketEquiv (s₀ : Structure.Automorphism act E) (C : Matrix I K) : J ≃ J := by
  let := TransversalPure.thinCommGroup S H R
  exact packetEquiv (rowStructural S H R B hB Δ A hA E hLocal s₀) C

/-- The packet permutation depends on the full rows, including distinct
rows above the same structural index. Every correction matrix is allowed. -/
def rowPCTransport (s₀ : Structure.Automorphism act E) (C : Matrix I K) :
    PCTransport (rowDiagram S H R B hB Δ A hA E hLocal)
      (rowDiagram S H R B hB Δ A hA E hLocal)
      (rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C) := by
  let := TransversalPure.thinCommGroup S H R
  apply Actual.pureGaugeTransport S H R B hB Δ hΔ
    (rowDiagram S H R B hB Δ A hA E hLocal)
    (rowDiagram S H R B hB Δ A hA E hLocal)
    (packetEquiv (rowStructural S H R B hB Δ A hA E hLocal s₀) C) s₀.lang
    (fun p => (rowStructural S H R B hB Δ A hA E hLocal s₀).offset p.1)
  intro p
  exact rowStructural_owner S H R B hB Δ A hA E hLocal s₀ p.1

end
end CCO.FullRows
