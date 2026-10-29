import CCO.RelativeMI.SafeRows
import CCO.RelativeMI.DecodedStructure
import CCO.RelativeMI.GlobalThin
import CCO.HKNReservoir.Consumer
import CCO.FullRows.Consumer

/-! The actual local constructor chooses ONE safe joint selector and ONE
reservoir/decoder before ALL original requests, including every empty
language component. The principal construction supplies this local source
and its safe system, rather than assuming any such witness exists. -/
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
local notation "act" => sourceAction S H R B Δ
local notation "tag" => sourceTag S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "W₀" => encode (decodedData S H R B hB Δ readingData hΔ A hA E hLocal c)

structure DecoderOutput (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1) where
  embedding : Structure.Embedding act W₀ (sourceStructure S H R B hB)
  embedding_lang : embedding.lang = 1
  source_fixed : ∀ a : A, embedding (zeroRowEmbed S H R B hB Δ A hA E hLocal j a) = a.val
  extends_original : ∀ p : Request tag D₀,
    ∃ g : Structure.Automorphism act W₀, g.lang = p.lang ∧
      ∀ a ∈ p.point.source,
        g (zeroRowEmbed S H R B hB Δ A hA E hLocal j a) =
          zeroRowEmbed S H R B hB Δ A hA E hLocal j (p.point a)

theorem DecoderOutput.every_language (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1)
    (out : DecoderOutput S H R B hB Δ readingData hΔ A hA E hLocal c j hj) (γ : Δ) :
    ∃ g : Structure.Automorphism act W₀, g.lang = γ := by
  obtain ⟨g,hg,_⟩ := out.extends_original (FullRows.originalEmptyRequest S H R B hB Δ A hA γ)
  exact ⟨g,hg⟩

omit [Finite Z] in
theorem safe_decoder_from_reservoir [Finite A]
    (safe : Set (S.Atom () ()))
    (hs : SafeSystem (TransversalSource.source S H R B) (orbitSafe S H R B hB safe))
    (r : CompletableReservoir S H R B hB Δ A hA (reservoirThreshold S H R B)) :
    ∃ q : JointReading S H R B hB Δ,
      q.SafeOn S H R B hB Δ (orbitSafe S H R B hB safe) ∧
      letI := r.stage.finiteNew
      Nonempty (DecoderOutput S H R B hB Δ q hΔ A hA r.stage.model
        (locallyInSource_of_faithful tag r.stage.inclusion r.stage.faithful)
        r.certificate r.stage.inclusion r.stage.inclusion_lang) := by
  obtain ⟨q,hq⟩ := exists_orbitSafe_jointReading S H R B hB Δ safe hs
  refine ⟨q,hq,?_⟩
  letI := r.stage.finiteNew
  let hL := locallyInSource_of_faithful tag r.stage.inclusion r.stage.faithful
  obtain ⟨e,he,hfix⟩ := alignedDecodedEmbedding S H R B hB Δ q hΔ A hA r.stage.model hL
    r.certificate r.stage.inclusion r.stage.inclusion_lang
  refine ⟨⟨e,he,hfix,?_⟩⟩
  intro p
  obtain ⟨s₀,hs,hpoint⟩ := r.extends_original p
  have hp : ∀ a ∈ p.point.source, s₀ (r.stage.inclusion a) = r.stage.inclusion (p.point a) := by
    intro a ha
    simpa only [r.stage.inclusion_apply] using hpoint a ha
  obtain ⟨C,hC,hzero⟩ := zeroRow_request_extension S H R B hB Δ A hA r.stage.model hL
    r.stage.inclusion p s₀ hp
  refine ⟨decodedLiftAut S H R B hB Δ q hΔ A hA r.stage.model hL r.certificate s₀ C hC,hs,?_⟩
  intro a ha
  exact hzero a ha

omit [Finite Z] in
theorem actual_safe_decoder [Finite A] (hne : A.Nonempty)
    (safe : Set (S.Atom () ()))
    (hs : SafeSystem (TransversalSource.source S H R B) (orbitSafe S H R B hB safe)) :
    ∃ r : CompletableReservoir S H R B hB Δ A hA (reservoirThreshold S H R B),
      ∃ q : JointReading S H R B hB Δ,
      q.SafeOn S H R B hB Δ (orbitSafe S H R B hB safe) ∧
      letI := r.stage.finiteNew
      Nonempty (DecoderOutput S H R B hB Δ q hΔ A hA r.stage.model
        (locallyInSource_of_faithful tag r.stage.inclusion r.stage.faithful)
        r.certificate r.stage.inclusion r.stage.inclusion_lang) := by
  obtain ⟨r⟩ := completable_reservoir S H R B hB Δ A hA hne
  exact ⟨r,safe_decoder_from_reservoir S H R B hB Δ hΔ A hA safe hs r⟩

end
end CCO.RelativeMI
