import CCO.FullRows.Defs
import CCO.FullRows.ReservoirCoordinates
import CCO.HKNReservoir.TypedOrigins
import CCO.OwnerTransversal.PacketCompletion

/-! Actual completion of ALL row clones. The certificate fixes the entire
chosen zero-row completion, while its unrecorded colours remain certificates
and are never installed as structural records. -/
universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
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
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "J" => Packet I K
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "tag" => sourceTag S H R B Δ

/-- Same-index distinct rows are holes because the structural diagonal is
none. The ACTUAL index is the full pair (i,f), never just i. -/
def clonePattern : OriginPattern S H R J where
  owner p := (sourceOriginPattern S H R B hB Δ A hA E hLocal).owner p.1
  edge p q := (sourceOriginPattern S H R B hB Δ A hA E hLocal).edge p.1 q.1
  symmetric p q := (sourceOriginPattern S H R B hB Δ A hA E hLocal).symmetric p.1 q.1
  diagonal p := (sourceOriginPattern S H R B hB Δ A hA E hLocal).diagonal p.1
  nonthin p q a := (sourceOriginPattern S H R B hB Δ A hA E hLocal).nonthin p.1 q.1 a

/-- The accepted B027 actual certificate supplies an origin map before
row separation; different rows over one i can initially coincide. -/
def cloneOrigins (c : PacketCertificate S H R B hB Δ A hA E hLocal) :
    OriginMap S H R B (clonePattern S H R B hB Δ A hA E hLocal) where
  point p := c.point (sourceOrigin S H R B hB Δ A hA E hLocal p.1)
  owner p := congrArg Subtype.val (c.owner _)
  edge p q a ha := c.fine a _ _ ((sourceOriginPattern_edge S H R B hB Δ A hA E hLocal p.1 q.1 a).mp ha)

theorem cloneOrigins_inflated (c : PacketCertificate S H R B hB Δ A hA E hLocal)
    (p : Vertex I K) :
    inflateOrigins S H R B hB (cloneOrigins S H R B hB Δ A hA E hLocal c).point p =
      c.point ((reservoirCoordinates S H R B hB Δ A hA E hLocal).symm (projection p)) := by
  exact (c.move p.2 (sourceOrigin S H R B hB Δ A hA E hLocal p.1.1)).symm

/-- Complete zero rows of ALL structural packets, not just the old A,
are a legitimate protected separated finite base of the actual certificate. -/
def zeroRows : Finset J := by
  classical
  letI : Fintype I := Fintype.ofFinite _
  exact Finset.univ.image (fun i : I => (i,fun _ => (1 : K)))

theorem mem_zeroRows (p : J) : p ∈ zeroRows S H R B E ↔ p.2 = fun _ => 1 := by
  classical
  simp only [zeroRows,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,he⟩
    exact (congrArg Prod.snd he).symm
  · intro he
    exact ⟨p.1,Prod.ext rfl he.symm⟩

/-- C10: invoke the accepted actual collision theorem on all literal row
packets, keeping the whole zero-row copy pointwise fixed. -/
theorem row_packet_completion (c : PacketCertificate S H R B hB Δ A hA E hLocal) :
    ∃ f : OriginMap S H R B (clonePattern S H R B hB Δ A hA E hLocal),
      Function.Injective (inflateOrigins S H R B hB f.point) ∧
      (∀ i z, inflateOrigins S H R B hB f.point ((i,fun _ => 1),z) =
        c.point ((reservoirCoordinates S H R B hB Δ A hA E hLocal).symm (i,z))) ∧
      ∀ i j a, (clonePattern S H R B hB Δ A hA E hLocal).edge i j = some a →
        ∀ g k : K, col S (inflateOrigins S H R B hB f.point (i,g)).val
          (inflateOrigins S H R B hB f.point (j,k)).val =
        col S (inflateOrigins S H R B hB (cloneOrigins S H R B hB Δ A hA E hLocal c).point (i,g)).val
          (inflateOrigins S H R B hB (cloneOrigins S H R B hB Δ A hA E hLocal c).point (j,k)).val := by
  classical
  letI : Finite K := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  letI : Fintype J := Fintype.ofFinite _
  let old := cloneOrigins S H R B hB Δ A hA E hLocal c
  have hi : Set.InjOn (inflateOrigins S H R B hB old.point) {p | p.1 ∈ zeroRows S H R B E} := by
    intro p hp q hq he
    have hp₀ := (mem_zeroRows S H R B E p.1).mp hp
    have hq₀ := (mem_zeroRows S H R B E q.1).mp hq
    have hcoord : projection p = projection q := by
      apply (reservoirCoordinates S H R B hB Δ A hA E hLocal).symm.injective
      apply c.injective
      exact (cloneOrigins_inflated S H R B hB Δ A hA E hLocal c p).symm.trans
        (he.trans (cloneOrigins_inflated S H R B hB Δ A hA E hLocal c q))
    have hi : p.1.1 = q.1.1 := congrArg (fun z : I × K => z.1) hcoord
    have hz : p.2 = q.2 := congrArg (fun z : I × K => z.2) hcoord
    exact Prod.ext (Prod.ext hi (hp₀.trans hq₀.symm)) hz
  obtain ⟨f,hf,hfix,_,hrec⟩ := OriginMap.packet_completion hB old (zeroRows S H R B E) hi
  refine ⟨f,hf,?_,hrec⟩
  intro i z
  exact (hfix ((i,fun _ => 1),z) ((mem_zeroRows S H R B E _).mpr rfl)).trans
    (cloneOrigins_inflated S H R B hB Δ A hA E hLocal c _)

/-- ONE initial diagram on ALL actual row packets. The diagonal structural
index contributes a same-owner diversity HOLE, never an equality atom. -/
def rowDiagram : PartialDiagram (SafeReadings.TransversalSource.source S H R B) J := by
  letI : Finite K := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  exact typedOriginDiagram S H R B (clonePattern S H R B hB Δ A hA E hLocal)
    (fun p => sourceOriginOwner S H R B hB Δ A hA E hLocal p.1)
    (fun p q a ha => sourceOriginPalette S H R B hB Δ A hA E hLocal p.1 q.1 a ha)

theorem rowDiagram_edge (p q : J) (hpq : p ≠ q)
    (a : (SafeReadings.TransversalSource.source S H R B).Atom
      (sourceOriginOwner S H R B hB Δ A hA E hLocal p.1)
      (sourceOriginOwner S H R B hB Δ A hA E hLocal q.1)) :
    (rowDiagram S H R B hB Δ A hA E hLocal).edge p q hpq = some a ↔
      (sourceOriginPattern S H R B hB Δ A hA E hLocal).edge p.1 q.1 = some a.val :=
  by
    letI : Finite K := translation_finite S (finitePacket S H) H (R.packet_thin S H)
    exact typedOriginEdge_some S H R B
      (clonePattern S H R B hB Δ A hA E hLocal)
      (fun r => sourceOriginOwner S H R B hB Δ A hA E hLocal r.1)
      (fun r s a ha => sourceOriginPalette S H R B hB Δ A hA E hLocal r.1 s.1 a ha) p q a

/-- C11: the actual clone completion gives an injective typed U origin
certificate for the SAME singleton/top initial PC domains. -/
theorem rowDiagram_strongCompletion
    (c : PacketCertificate S H R B hB Δ A hA E hLocal) :
    (rowDiagram S H R B hB Δ A hA E hLocal).HasStrongCompletion := by
  classical
  letI : Finite K := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  obtain ⟨f,hf,_,_⟩ := row_packet_completion S H R B hB Δ A hA E hLocal c
  have hsep : ∀ p q : J, p ≠ q → ¬finitePacket S H (f.point p).val (f.point q).val := by
    intro p q hpq hF
    obtain ⟨g,hg,_⟩ := translation_regular S (finitePacket S H) H (R.packet_thin S H)
      (f.point p).val (f.point q).val hF
    have he : inflateOrigins S H R B hB f.point (p,g) =
        inflateOrigins S H R B hB f.point (q,1) := by
      exact (Subtype.ext hg).trans (packetPoint_one S H R B hB (f.point q)).symm
    exact hpq (congrArg (fun z : J × K => z.1) (hf he))
  obtain ⟨u,ho,hc⟩ := TransversalAge.embed_origins S H R B f.point hsep
  have howner (p : J) : TransversalAge.ownerLabel S H R B (f.point p) =
      sourceOriginOwner S H R B hB Δ A hA E hLocal p.1 := Subtype.ext (f.owner p)
  let point (p : J) : SafeReadings.TransversalSource.Carrier S H R B
      (sourceOriginOwner S H R B hB Δ A hA E hLocal p.1) := ⟨u p,(ho p).trans (howner p)⟩
  let hom : DiagramHom (rowDiagram S H R B hB Δ A hA E hLocal) := {
    point := point
    preserves_edge := by
      intro p q hpq a ha
      apply (SafeReadings.TransversalSource.colour_some_iff S H R B _ _ a).mpr
      exact (hc p q).trans (f.edge p q a.val ((rowDiagram_edge S H R B hB Δ A hA E hLocal p q hpq a).mp ha)) }
  refine ⟨hom,?_⟩
  intro p q he
  exact u.injective (congrArg (SafeReadings.TransversalSource.sigmaEquiv S H R B) he)
end
end CCO.FullRows
