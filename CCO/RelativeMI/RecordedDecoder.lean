import CCO.FullRows.RecordedDecoder
import CCO.RelativeMI.ExplicitDecoder
import CCO.StrongExact.PCSoundness

/-! Every original recorded singleton/matrix remains literal in the ONE
decoder, independently of the later correction parameters. -/
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
local notation "D" => rowDiagram S H R B hB Δ A hA E hLocal
local notation "P" => sourceOriginPattern S H R B hB Δ A hA E hLocal

theorem originAtom_record (p q : J) (hpq : p ≠ q) (a : S.Atom () ())
    (ha : (P).edge p.1 q.1 = some a) :
    (originAtom S H R B hB Δ readingData hΔ A hA E hLocal c ⟨p,q,hpq⟩).val = a := by
  letI := TransversalPure.thinCommGroup S H R
  obtain ⟨b,hb,hm⟩ := rowFixed_record S H R B hB Δ A hA E hLocal c p q hpq a ha
  have hmem := parametricReading_member S H R B hB Δ readingData hΔ
    (parameter (p,1) (q,1)) (rowFixedMenu S H R B hB Δ A hA E hLocal ⟨p,q,hpq⟩)
    (rowFixed_exact S H R B hB Δ A hA E hLocal c ⟨p,q,hpq⟩)
  have hsingle := (Set.ext_iff.mp hm _).mp hmem
  exact (congrArg Subtype.val (Set.mem_singleton_iff.mp hsingle)).trans hb

theorem decodedColour_recorded_matrix (x y : Vertex I K) (a : S.Atom () ())
    (ha : (P).edge x.1.1 y.1.1 = some a) :
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y =
      switchColour S (finitePacket S H) (x.2*y.2) (some a) := by
  have hxy : x.1 ≠ y.1 := by
    intro he
    have hh := congrArg Prod.fst he
    rw [hh,(P).diagonal] at ha
    cases ha
  simp only [decodedColour,dif_neg hxy,originAtom_record S H R B hB Δ readingData hΔ A hA E hLocal c x.1 y.1 hxy a ha]

/-- Preservation of every sparse clone record. Same actual packets retain
the complete thin matrix; distinct recorded structural pairs retain all entries. -/
theorem decodedColour_sparse_record (x y : Vertex I K) (a : S.Atom () ())
    (hrecord : x.1 = y.1 ∨ ∃ b, (P).edge x.1.1 y.1.1 = some b)
    (ha : E.rel (.fine a) (![(reservoirCoordinates S H R B hB Δ A hA E hLocal).symm (projection x),
      (reservoirCoordinates S H R B hB Δ A hA E hLocal).symm (projection y)])) :
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y = some a := by
  rcases hrecord with hxy | ⟨b,hb⟩
  · rcases x with ⟨p,g⟩
    rcases y with ⟨q,k⟩
    cases hxy
    have hh := (recovered_internal_fine S H R B hB (sourceTag S H R B Δ) A hA E hLocal
      (sourceOrigin S H R B hB Δ A hA E hLocal p.1) g k a).mp ha
    simpa only [decodedColour,dite_true] using hh
  · rw [decodedColour_recorded_matrix S H R B hB Δ readingData hΔ A hA E hLocal c x y b hb]
    exact (recovered_matrix_law S H R B hB (sourceTag S H R B Δ) A hA E hLocal
      (sourceOrigin S H R B hB Δ A hA E hLocal x.1.1)
      (sourceOrigin S H R B hB Δ A hA E hLocal y.1.1) b
      ((sourceOriginPattern_edge S H R B hB Δ A hA E hLocal _ _ b).mp hb) x.2 y.2 a).mp ha
end
end CCO.RelativeMI
