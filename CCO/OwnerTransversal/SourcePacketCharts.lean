import CCO.OwnerTransversal.InflationBasic
import CCO.OwnerTransversal.PacketLanguage
import CCO.OwnerTransversal.PacketCharts

/-! Actual regular packets on every full finite named-source substructure.
Packet labels are quotient classes of the ORIGINAL finite equivalence;
owner labels are retained separately and need not determine a packet. -/

open scoped FirstOrder
open FirstOrder FirstOrder.Language

universe v w t
namespace CCO.OwnerTransversal.Inflation
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization PacketCoordinates

variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

local notation "SourceSubstructure" =>
  @FirstOrder.Language.Substructure
    (PacketLanguage.language (ResidualData.PacketGroup S H) {q : Owner S H R // q ∈ B} (FullColour S))
    (NamedCarrier S H R B)
    (@PacketLanguage.ofTable (ResidualData.PacketGroup S H) inferInstance
      {q : Owner S H R // q ∈ B} (FullColour S) (NamedCarrier S H R B)
      (packetNamedAction S H R B hB) (namedTable S H R B))

/-- The packet equivalence on the actual points of a full substructure. -/
def packetSetoid (D : SourceSubstructure) : Setoid D :=
  Setoid.comap (fun x : D => x.val.val) (finitePacket S H).val

abbrev PacketIndex (D : SourceSubstructure) :=
  Quotient (packetSetoid S H R B hB D)

def packet (D : SourceSubstructure) (p : D) :
    PacketIndex S H R B hB D := Quotient.mk (packetSetoid S H R B hB D) p

/-- Literal packet equality is recognized by the actual original F. -/
theorem packet_eq (D : SourceSubstructure) (p q : D) :
    packet S H R B hB D p = packet S H R B hB D q ↔
      finitePacket S H p.val.val q.val.val := Quotient.eq

instance finitePacketIndex (D : SourceSubstructure) [Finite D] :
    Finite (PacketIndex S H R B hB D) :=
  Finite.of_surjective (packet S H R B hB D) (by
    intro q
    exact Quotient.inductionOn q (fun p => ⟨p,rfl⟩))

/-- Each packet is an entire regular translation orbit inside D: closure
under all named functions is used, with no owner-faithfulness premise. -/
def packets (D : SourceSubstructure) :
    letI := packetNamedAction S H R B hB
    letI := PacketLanguage.ofTable (K := ResidualData.PacketGroup S H) (namedTable S H R B)
    letI := PacketLanguage.subaction (K := ResidualData.PacketGroup S H) (namedTable S H R B) D
    RegularPackets (K := ResidualData.PacketGroup S H) (P := D)
      (I := PacketIndex S H R B hB D) := by
  letI := packetNamedAction S H R B hB
  letI := PacketLanguage.ofTable (K := ResidualData.PacketGroup S H) (namedTable S H R B)
  letI := PacketLanguage.subaction (K := ResidualData.PacketGroup S H) (namedTable S H R B) D
  exact {
    packet := packet S H R B hB D
    onto := by
      intro q
      exact Quotient.inductionOn q (fun p => ⟨p,rfl⟩)
    invariant := by
      intro g p
      apply (packet_eq S H R B hB D _ _).mpr
      exact (finitePacket S H).val.symm
        (translation_in_packet S (finitePacket S H) G g p.val.val)
    regular := by
      intro p q hpq
      have hF := (packet_eq S H R B hB D p q).mp hpq
      obtain ⟨g,hg,hu⟩ := translation_regular S (finitePacket S H) H
        (R.packet_thin S H) p.val.val q.val.val hF
      refine ⟨g,Subtype.ext (Subtype.ext hg),?_⟩
      intro f hf
      exact hu f (congrArg (fun x : D => x.val.val) hf) }

end
end CCO.OwnerTransversal.Inflation
