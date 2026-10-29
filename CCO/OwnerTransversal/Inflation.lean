import CCO.OwnerTransversal.InflationExtension
import CCO.OwnerTransversal.InflationRealization

/-! Actual countable recovery from BOTH discharged finite FULL-packet
extension properties. Every literal owner, original fine colour and t_g is
preserved, including a prescribed finite old full-packet embedding. -/
open scoped FirstOrder
open FirstOrder FirstOrder.Language
universe v w t
namespace CCO.OwnerTransversal.Inflation
noncomputable section
open ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Geometry FinitePackets.Normalization CountableColour TransversalAge
variable {M : Type v} (S : AtomicSource.{0,v,w} Unit (fun _ => M))
variable {G : Type t} [Group G] [MulAction G M] (H : HomogeneousSource S G)
variable [Countable M] [DecidableEq M] [Infinite M] (R : ResidualData S H)
variable (B : Finset (Owner S H R)) (hB : PacketInvariant S H R B)

theorem source_locallyFinite :
    letI := sourceStructure S H R B hB
    PacketBackAndForth.LocallyFinite (Signature S H R B) (NamedCarrier S H R B) := by
  letI := packetNamedAction S H R B hB
  letI : Finite (ResidualData.PacketGroup S H) := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  exact PacketLanguage.locallyFinite (namedTable S H R B)

theorem inflation_locallyFinite :
    letI := inflationStructure S H R B hB
    PacketBackAndForth.LocallyFinite (Signature S H R B) (Carrier S H R B) := by
  letI := action S H R B
  letI : Finite (ResidualData.PacketGroup S H) := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  exact PacketLanguage.locallyFinite (table S H R B hB)

/-- C46 with a prescribed finite base: all source hypotheses and BOTH
finite full-packet extension instances are actually discharged above. -/
theorem recovery_extending
    (A : @Substructure (Signature S H R B) (NamedCarrier S H R B) (sourceStructure S H R B hB))
    [Finite A]
    (f : letI := sourceStructure S H R B hB
      letI := inflationStructure S H R B hB
      A ↪[Signature S H R B] Carrier S H R B) :
    letI := sourceStructure S H R B hB
    letI := inflationStructure S H R B hB
    ∃ e : NamedCarrier S H R B ≃[Signature S H R B] Carrier S H R B,
      e.toEmbedding.comp A.subtype = f := by
  letI := sourceStructure S H R B hB
  letI := inflationStructure S H R B hB
  letI : Finite (ResidualData.PacketGroup S H) := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  exact PacketBackAndForth.equiv_extending (Signature S H R B)
    (NamedCarrier S H R B) (Carrier S H R B)
    (source_locallyFinite S H R B hB) (inflation_locallyFinite S H R B hB)
    (finite_extension_to_inflation S H R B hB) (finite_extension_to_source S H R B hB) A f

/-- Countable recovery in the conventional inflation→source direction,
with every point of the prescribed old finite full-packet copy fixed. -/
theorem recovery_inverse_extending
    (A : @Substructure (Signature S H R B) (NamedCarrier S H R B) (sourceStructure S H R B hB))
    [Finite A]
    (f : letI := sourceStructure S H R B hB
      letI := inflationStructure S H R B hB
      A ↪[Signature S H R B] Carrier S H R B) :
    letI := sourceStructure S H R B hB
    letI := inflationStructure S H R B hB
    ∃ e : Carrier S H R B ≃[Signature S H R B] NamedCarrier S H R B,
      ∀ a : A, e (f a) = a.val := by
  letI := sourceStructure S H R B hB
  letI := inflationStructure S H R B hB
  obtain ⟨e,he⟩ := recovery_extending S H R B hB A f
  refine ⟨e.symm,?_⟩
  intro a
  rw [← DFunLike.congr_fun he a]
  exact e.symm_apply_apply a.val

/-- The internally constructed full inflation recovers the ACTUAL named
source. The empty owner collection is a valid stronger boundary case. -/
theorem recovery :
    letI := sourceStructure S H R B hB
    letI := inflationStructure S H R B hB
    Nonempty (Carrier S H R B ≃[Signature S H R B] NamedCarrier S H R B) := by
  letI := sourceStructure S H R B hB
  letI := inflationStructure S H R B hB
  letI : IsEmpty (Signature S H R B).Constants := ⟨fun f => by cases f⟩
  letI : IsEmpty ((Signature S H R B).Relations 0) := ⟨fun r => by cases r⟩
  let p : (Signature S H R B).FGEquiv (NamedCarrier S H R B) (Carrier S H R B) := default
  letI : Finite p.val.dom := source_locallyFinite S H R B hB p.val.dom p.property
  obtain ⟨e,_⟩ := recovery_extending S H R B hB p.val.dom p.val.toEmbedding
  exact ⟨e.symm⟩

/-- All literal readouts of the actual recovery, independently of any
chosen origin section, follow from its genuine full language equivalence. -/
theorem recovery_readout :
    ∃ e : Carrier S H R B ≃ NamedCarrier S H R B,
      (∀ x, ownerLabel S H R B (e x) = (table S H R B hB).owner x) ∧
      (∀ x y, col S (e x).val (e y).val = (table S H R B hB).colour x y) ∧
      ∀ (g : ResidualData.PacketGroup S H) x,
        e ((action S H R B).smul g x) = packetPoint S H R B hB g (e x) := by
  letI := packetNamedAction S H R B hB
  letI := action S H R B
  letI := sourceStructure S H R B hB
  letI := inflationStructure S H R B hB
  obtain ⟨e⟩ := recovery S H R B hB
  have hp := PacketLanguage.embedding_preserves (table S H R B hB) (namedTable S H R B) e.toEmbedding
  exact ⟨e.toEquiv,hp⟩

end
end CCO.OwnerTransversal.Inflation
