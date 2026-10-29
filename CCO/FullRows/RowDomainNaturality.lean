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


omit [Finite Z] [Infinite M] in
private theorem rawAut_fine (s₀ : Structure.Automorphism act E) (x y : Z) (a : S.Atom () ()) :
    E.rel (.fine a) (![s₀ x,s₀ y]) ↔ E.rel (.fine a) (![x,y]) := by
  have hh := (automorphismEmbedding tag s₀).map_rel_iff (.fine a) (![x,y])
  change E.rel (.fine a) ((fun z => s₀ z) ∘ ![x,y]) ↔ E.rel (.fine a) (![x,y]) at hh
  have ht : (fun z => s₀ z) ∘ (![x,y] : Fin 2 → Z) = ![s₀ x,s₀ y] := by
    funext i; fin_cases i <;> rfl
  rw [ht] at hh
  exact hh

private theorem rowPCTransport_colour (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (p : DistinctPair J) (a : (SafeReadings.TransversalSource.source S H R B).Atom
      ((rowDiagram S H R B hB Δ A hA E hLocal).vertexSort p.src)
      ((rowDiagram S H R B hB Δ A hA E hLocal).vertexSort p.dst)) :
    some ((rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).atom p a).val =
      switchColour S (finitePacket S H)
        ((rowStructural S H R B hB Δ A hA E hLocal s₀).offset p.src.1 *
          (rowStructural S H R B hB Δ A hA E hLocal s₀).offset p.dst.1) (some a.val) := by
  let := TransversalPure.thinCommGroup S H R
  let D := rowDiagram S H R B hB Δ A hA E hLocal
  let P := TransversalPure.subgroupRelabelling S H R B hB Δ
  let Q := TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  have hh := pureGaugeTransport_label D D (packetEquiv s C) P Q s₀.lang
    (fun p => s.offset p.1)
    (fun p => rowStructural_owner S H R B hB Δ A hA E hLocal s₀ p.1) p a
  change some ((rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).atom p a).val =
    switchColour S (finitePacket S H) (s.offset p.src.1)
      (switchColour S (finitePacket S H) (s.offset p.dst.1) (some a.val)) at hh
  rw [← switchColour_mul S (finitePacket S H) H] at hh
  exact hh


private theorem rowPCTransport_fine_iff (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (p : DistinctPair J) (a : (TransversalSource.source S H R B).Atom
      ((rowDiagram S H R B hB Δ A hA E hLocal).vertexSort p.src)
      ((rowDiagram S H R B hB Δ A hA E hLocal).vertexSort p.dst)) :
    E.rel (.fine ((rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).atom p a).val)
      (![org ((rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C p.src).1),
        org ((rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C p.dst).1)]) ↔
      E.rel (.fine a.val) (![org p.src.1,org p.dst.1]) := by
  let := TransversalPure.thinCommGroup S H R
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  let a' := (rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).atom p a
  have hColor : some a'.val = switchColour S (finitePacket S H)
      (s.offset p.src.1 * s.offset p.dst.1) (some a.val) :=
    rowPCTransport_colour S H R B hB Δ hΔ A hA E hLocal s₀ C p a
  have hBackColor : switchColour S (finitePacket S H)
      (s.offset p.src.1 * s.offset p.dst.1) (some a'.val) = some a.val := by
    rw [hColor]
    exact switchColour_involutive S (finitePacket S H) H (R.packet_thin S H) _ _
  have hback (i : I) : move (s.offset i) (s₀ (org i)) = org (s.sigma i) := by
    rw [rowStructural_origin, ← PacketRecovery.move_mul tag D₀ E hLocal
      (finiteSource_regularData S H R B hB A hA),
      translation_square S (finitePacket S H) H (R.packet_thin S H),
      PacketRecovery.move_one tag D₀ E hLocal (finiteSource_regularData S H R B hB A hA)]
  change E.rel (.fine a'.val) (![org (s.sigma p.src.1),org (s.sigma p.dst.1)]) ↔ _
  constructor
  · intro ha
    have hm := (recovered_matrix_law S H R B hB tag A hA E hLocal
      (org (s.sigma p.src.1)) (org (s.sigma p.dst.1)) a'.val ha
      (s.offset p.src.1) (s.offset p.dst.1) a.val).mpr hBackColor
    rw [← rowStructural_origin S H R B hB Δ A hA E hLocal s₀ p.src.1,
      ← rowStructural_origin S H R B hB Δ A hA E hLocal s₀ p.dst.1] at hm
    exact (rawAut_fine S H R B Δ E s₀ _ _ _).mp hm
  · intro ha
    have hm := (rawAut_fine S H R B Δ E s₀ _ _ _).mpr ha
    have ht := (recovered_matrix_law S H R B hB tag A hA E hLocal
      (s₀ (org p.src.1)) (s₀ (org p.dst.1)) a.val hm
      (s.offset p.src.1) (s.offset p.dst.1) a'.val).mpr hColor.symm
    simpa only [hback] using ht

/-- Exact record reflection covers both directions; consequently holes
are preserved too, including all same-index distinct-row packet pairs. -/
theorem rowPCTransport_record_iff (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (p : DistinctPair J) (a : (TransversalSource.source S H R B).Atom
      ((rowDiagram S H R B hB Δ A hA E hLocal).vertexSort p.src)
      ((rowDiagram S H R B hB Δ A hA E hLocal).vertexSort p.dst)) :
    (rowDiagram S H R B hB Δ A hA E hLocal).edge
      (rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C p.src)
      (rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C p.dst)
      (fun h => p.ne ((rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C).injective h)) =
      some ((rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).atom p a) ↔
    (rowDiagram S H R B hB Δ A hA E hLocal).edge p.src p.dst p.ne = some a := by
  let π := rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C
  let a' := (rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).atom p a
  exact (rowDiagram_edge S H R B hB Δ A hA E hLocal (π p.src) (π p.dst)
    (fun h => p.ne (π.injective h)) a').trans
    ((sourceOriginPattern_edge S H R B hB Δ A hA E hLocal (π p.src).1 (π p.dst).1 a'.val).trans
      ((rowPCTransport_fine_iff S H R B hB Δ hΔ A hA E hLocal s₀ C p a).trans
        ((sourceOriginPattern_edge S H R B hB Δ A hA E hLocal p.src.1 p.dst.1 a.val).symm.trans
          (rowDiagram_edge S H R B hB Δ A hA E hLocal p.src p.dst p.ne a).symm)))

theorem row_initial_natural (s₀ : Structure.Automorphism act E) (C : Matrix I K) :
    (rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).networkIso
      (StrongPC.initial (rowDiagram S H R B hB Δ A hA E hLocal)) =
    StrongPC.initial (rowDiagram S H R B hB Δ A hA E hLocal) := by
  let D := rowDiagram S H R B hB Δ A hA E hLocal
  let T := rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C
  apply T.initial_natural_of_edges
  intro p
  cases he : D.edge p.src p.dst p.ne with
  | some a =>
      simpa only [he,Option.map_some] using
        (rowPCTransport_record_iff S H R B hB Δ hΔ A hA E hLocal s₀ C p a).mpr he
  | none =>
      rw [Option.map_none]
      cases ht : D.edge
        (rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C p.src)
        (rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C p.dst)
        (fun h => p.ne ((rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C).injective h)) with
      | none => rfl
      | some a' =>
          obtain ⟨a,rfl⟩ := (T.atom p).surjective a'
          have hh := (rowPCTransport_record_iff S H R B hB Δ hΔ A hA E hLocal s₀ C p a).mp ht
          rw [he] at hh
          cases hh

theorem row_fixedNetwork_natural (s₀ : Structure.Automorphism act E) (C : Matrix I K) :
    (rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).networkIso
      (StrongPC.fixedNetwork (rowDiagram S H R B hB Δ A hA E hLocal)) =
    StrongPC.fixedNetwork (rowDiagram S H R B hB Δ A hA E hLocal) :=
  (rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C).fixedNetwork_natural
    (row_initial_natural S H R B hB Δ hΔ A hA E hLocal s₀ C)

end
end CCO.FullRows
