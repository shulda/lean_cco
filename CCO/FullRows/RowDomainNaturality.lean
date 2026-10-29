import CCO.FullRows.RowCertificate
import CCO.FullRows.GaugeNatural
import CCO.FullRows.Rows
import CCO.FullRows.StructuralCoordinates
import CCO.FullRows.VertexDomains

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


def rowVertexEquiv (s₀ : Structure.Automorphism act E) (C : Matrix I K) :
    Vertex I K ≃ Vertex I K := by
  let := TransversalPure.thinCommGroup S H R
  exact liftEquiv (rowStructural S H R B hB Δ A hA E hLocal s₀) C

omit [Finite Z] in
theorem rowVertexEquiv_packet_ne (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (x y : Vertex I K) (hxy : x.1 ≠ y.1) :
    (rowVertexEquiv S H R B hB Δ A hA E hLocal s₀ C x).1 ≠
      (rowVertexEquiv S H R B hB Δ A hA E hLocal s₀ C y).1 :=
  fun h => hxy ((rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C).injective h)

omit [Finite Z] in
theorem rowVertexEquiv_owner (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (x : Vertex I K) :
    vertexOwner S H R B hB Δ A hA E hLocal
      (rowVertexEquiv S H R B hB Δ A hA E hLocal s₀ C x) =
    (TransversalPure.subgroupRelabelling S H R B hB Δ).owner s₀.lang
      (vertexOwner S H R B hB Δ A hA E hLocal x) := by
  let := TransversalPure.thinCommGroup S H R
  let Q := TransversalPure.endpointGauge S H R B hB
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  change Q.owner (x.2*s.offset x.1.1) (own (s.sigma x.1.1)) =
    (TransversalPure.subgroupRelabelling S H R B hB Δ).owner s₀.lang (Q.owner x.2 (own x.1.1))
  have hOwner : own (s.sigma x.1.1) = Q.owner (s.offset x.1.1)
      ((TransversalPure.subgroupRelabelling S H R B hB Δ).owner s₀.lang (own x.1.1)) :=
    rowStructural_owner S H R B hB Δ A hA E hLocal s₀ x.1.1
  calc
    _ = Q.owner x.2 (Q.owner (s.offset x.1.1) (own (s.sigma x.1.1))) :=
      congrArg (fun e : Equiv.Perm ↥B => e (own (s.sigma x.1.1)))
        (Q.owner.map_mul x.2 (s.offset x.1.1))
    _ = Q.owner x.2 (Q.owner (s.offset x.1.1) (Q.owner (s.offset x.1.1)
        ((TransversalPure.subgroupRelabelling S H R B hB Δ).owner s₀.lang (own x.1.1)))) :=
      congrArg (fun b => Q.owner x.2 (Q.owner (s.offset x.1.1) b)) hOwner
    _ = Q.owner x.2 ((TransversalPure.subgroupRelabelling S H R B hB Δ).owner s₀.lang (own x.1.1)) :=
      congrArg (Q.owner x.2) (Q.owner_twice (s.offset x.1.1) _)
    _ = _ := (Q.commute s₀.lang.val x.2 (own x.1.1)).symm

private theorem gauge_raw_names (g h : K) {i j : ↥B}
    (M : (TransversalSource.source S H R B).Menu i j) :
    letI := TransversalPure.thinCommGroup S H R
    (fun a => some a.val) ''
      gaugeMenu (TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ) g h M =
      switchColour S (finitePacket S H) (g*h) '' ((fun a => some a.val) '' M) := by
  let := TransversalPure.thinCommGroup S H R
  let Q := TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  simp only [gaugeMenu,Set.image_image]
  congr 1
  funext a
  change (TransversalPure.subgroupAction S H R B hB Δ).label (Q.left g (Q.right h a)) = _
  rw [Q.left_label,Q.right_label]
  exact (switchColour_mul S (finitePacket S H) H g h (some a.val)).symm

include hΔ in
private theorem row_fixed_raw_names (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (p : DistinctPair J) :
    (fun a => some a.val) '' StrongPC.fixedNetwork (rowDiagram S H R B hB Δ A hA E hLocal)
      (pairEquiv (rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C) p) =
    switchColour S (finitePacket S H)
      ((rowStructural S H R B hB Δ A hA E hLocal s₀).offset p.src.1 *
        (rowStructural S H R B hB Δ A hA E hLocal s₀).offset p.dst.1) ''
      ((fun a => some a.val) '' StrongPC.fixedNetwork
        (rowDiagram S H R B hB Δ A hA E hLocal) p) := by
  let T := rowPCTransport S H R B hB Δ hΔ A hA E hLocal s₀ C
  have hm := congrFun (row_fixedNetwork_natural S H R B hB Δ hΔ A hA E hLocal s₀ C)
    (pairEquiv (rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C) p)
  rw [T.networkIso_apply] at hm
  rw [← hm,Set.image_image,Set.image_image]
  congr 1
  funext a
  exact rowPCTransport_colour S H R B hB Δ hΔ A hA E hLocal s₀ C p a

/-- Full vertex domains have the SAME literal original fine names after
every actual full-row lift. The two image phases cancel the real offsets. -/
theorem vertexDomain_raw_covariant (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (x y : Vertex I K) (hxy : x.1 ≠ y.1) :
    (fun a => some a.val) '' vertexDomain S H R B hB Δ hΔ A hA E hLocal
      (rowVertexEquiv S H R B hB Δ A hA E hLocal s₀ C x)
      (rowVertexEquiv S H R B hB Δ A hA E hLocal s₀ C y)
      (rowVertexEquiv_packet_ne S H R B hB Δ A hA E hLocal s₀ C x y hxy) =
    (fun a => some a.val) '' vertexDomain S H R B hB Δ hΔ A hA E hLocal x y hxy := by
  let := TransversalPure.thinCommGroup S H R
  let Q := TransversalPure.subgroupEndpointGauge S H R B hB Δ hΔ
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  let D := rowDiagram S H R B hB Δ A hA E hLocal
  change (fun a => some a.val) '' gaugeMenu Q (x.2*s.offset x.1.1) (y.2*s.offset y.1.1)
    (StrongPC.fixedNetwork D (pairEquiv (rowPacketEquiv S H R B hB Δ A hA E hLocal s₀ C)
      ⟨x.1,y.1,hxy⟩)) =
    (fun a => some a.val) '' gaugeMenu Q x.2 y.2 (StrongPC.fixedNetwork D ⟨x.1,y.1,hxy⟩)
  rw [gauge_raw_names S H R B hB Δ hΔ,
    gauge_raw_names S H R B hB Δ hΔ,
    row_fixed_raw_names S H R B hB Δ hΔ A hA E hLocal s₀ C ⟨x.1,y.1,hxy⟩,
    Set.image_image]
  have hFront : (x.2*s.offset x.1.1)*(y.2*s.offset y.1.1) =
      (x.2*y.2)*(s.offset x.1.1*s.offset y.1.1) := by
    rw [mul_assoc, ← mul_assoc (s.offset x.1.1) y.2 (s.offset y.1.1),
      translation_comm S (finitePacket S H) H (R.packet_thin S H) (s.offset x.1.1) y.2,
      mul_assoc, ← mul_assoc]
  have hc : ((x.2*s.offset x.1.1)*(y.2*s.offset y.1.1)) *
      (s.offset x.1.1*s.offset y.1.1) = x.2*y.2 := by
    rw [hFront,mul_assoc,translation_square S (finitePacket S H) H (R.packet_thin S H),mul_one]
  congr 1
  funext c
  rw [← switchColour_mul S (finitePacket S H) H]
  exact congrArg (fun g => switchColour S (finitePacket S H) g c) hc


omit [Finite Z] in
/-- The vertex-owner equation in the literal `lift` notation and the
original globally prescribed language component. -/
theorem rowLift_vertexOwner (s₀ : Structure.Automorphism act E) (C : Matrix I K)
    (x : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    vertexOwner S H R B hB Δ A hA E hLocal
      (lift (rowStructural S H R B hB Δ A hA E hLocal s₀) C x) =
      sourceTag S H R B Δ s₀.lang (vertexOwner S H R B hB Δ A hA E hLocal x) := by
  let := TransversalPure.thinCommGroup S H R
  exact rowVertexEquiv_owner S H R B hB Δ A hA E hLocal s₀ C x

end
end CCO.FullRows
