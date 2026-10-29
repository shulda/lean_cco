import CCO.FullRows.DecodedStructure
import CCO.FullRows.GlobalThin
import CCO.FullRows.OrbitTrim
import CCO.FullRows.SemilinearImage
import CCO.FullRows.RowObstructions
import CCO.HKNReservoir.Consumer

/-! The end-to-end source consumer fixes ONE reservoir, all full rows,
ONE greatest PC network and ONE fine decoder before ALL requests/lifts. -/
universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge
open SafeReadings Selectors
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
variable (c : PacketCertificate S H R B hB Δ A hA E hLocal)
set_option quotPrecheck false
local notation "K" => ResidualData.PacketGroup S H
local notation "I" => PacketRecovery.PacketIndex E
local notation "tag" => sourceTag S H R B Δ
local notation "act" => sourceAction S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "W₀" => encode (decodedData S H R B hB Δ hΔ A hA E hLocal c)

structure RowOutput (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1) where
  embedding : Structure.Embedding act W₀ (sourceStructure S H R B hB)
  embedding_lang : embedding.lang = 1
  source_fixed : ∀ a : A, embedding (zeroRowEmbed S H R B hB Δ A hA E hLocal j a) = a.val
  extends_original : ∀ p : Request tag D₀,
    ∃ g : Structure.Automorphism act W₀, g.lang = p.lang ∧
      ∀ a ∈ p.point.source,
        g (zeroRowEmbed S H R B hB Δ A hA E hLocal j a) =
          zeroRowEmbed S H R B hB Δ A hA E hLocal j (p.point a)

/-- Original empty real domains retain EVERY independently prescribed
ENTIRE owner-language component. -/
def originalEmptyRequest (γ : Δ) : Request tag D₀ where
  lang := γ
  point := PartialEquiv.ofSet ∅
  owner := by intro a ha; exact False.elim ha
  fine := by intro d a b ha; exact False.elim ha

theorem RowOutput.every_language (j : Structure.Embedding act (encode D₀) E) (hj : j.lang=1)
    (r : RowOutput S H R B hB Δ hΔ A hA E hLocal c j hj) (γ : Δ) :
    ∃ g : Structure.Automorphism act W₀, g.lang = γ := by
  obtain ⟨g,hg,_⟩ := r.extends_original (originalEmptyRequest S H R B hB Δ A hA γ)
  exact ⟨g,hg⟩

/-- The one fixed decoder has exactly ALL full functions as rows. -/
theorem decoded_cardinality :
    Nat.card (Vertex I K) = Nat.card I * Nat.card K ^ (Nat.card I+1) := by
  classical
  letI := TransversalPure.thinCommGroup S H R
  letI : Finite K := translation_finite S (finitePacket S H) H (R.packet_thin S H)
  letI : Fintype I := Fintype.ofFinite _
  letI : Fintype K := Fintype.ofFinite _
  have hc : Fintype.card (Vertex I K) = Fintype.card I * Fintype.card K ^ (Fintype.card I+1) := vertex_card
  simpa only [Nat.card_eq_fintype_card] using hc

/-- Simultaneous whole-packet zeroing is an actual automorphism of THIS
same decoder, without promising to fix unrelated old zero-row packets. -/
theorem decoded_recorded_clique_zeroing
    (s₀ : Structure.Automorphism act E)
    (T : Set I) (hT : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → recordedPairs S H R B hB Δ A hA E hLocal i j)
    (f : I → Row I K) :
    letI := TransversalPure.thinCommGroup S H R
    ∃ g : Structure.Automorphism act W₀, g.lang = s₀.lang ∧
      ∀ i ∈ T, ∀ z : K, g ((i,f i),z) =
        (((rowStructural S H R B hB Δ A hA E hLocal s₀).sigma i,1),
          z*(rowStructural S H R B hB Δ A hA E hLocal s₀).offset i) := by
  letI := TransversalPure.thinCommGroup S H R
  let s := rowStructural S H R B hB Δ A hA E hLocal s₀
  obtain ⟨C,hC,hzero,_⟩ := recorded_clique_zeroing
    (fun g => translation_square S (finitePacket S H) H (R.packet_thin S H) g) s
    (recordedPairs S H R B hB Δ A hA E hLocal)
    (recordedPairs_symmetric S H R B hB Δ A hA E hLocal) T hT f
  refine ⟨decodedLiftAut S H R B hB Δ hΔ A hA E hLocal c s₀ C hC,rfl,?_⟩
  intro i hi z
  change ((s.sigma i,rowImage s C i (f i)),z*s.offset i) = _
  exact congrArg (fun r : Row I K => ((s.sigma i,r),z*s.offset i)) (hzero i hi)

omit [Finite Z] in
/-- ACTUAL relative-owner R07: instantiate the accepted reservoir and all
completion/reading/age obligations before choosing ANY request correction. -/
theorem actual_relative_witness [Finite A] (hne : A.Nonempty) :
    ∃ r : CompletableReservoir S H R B hB Δ A hA (reservoirThreshold S H R B),
      letI := r.stage.finiteNew
      Nonempty (RowOutput S H R B hB Δ hΔ A hA r.stage.model
        (locallyInSource_of_faithful tag r.stage.inclusion r.stage.faithful)
        r.certificate r.stage.inclusion r.stage.inclusion_lang) := by
  obtain ⟨r⟩ := completable_reservoir S H R B hB Δ A hA hne
  refine ⟨r,?_⟩
  letI := r.stage.finiteNew
  let hL := locallyInSource_of_faithful tag r.stage.inclusion r.stage.faithful
  obtain ⟨e,he,hfix⟩ := alignedDecodedEmbedding S H R B hB Δ hΔ A hA r.stage.model hL
    r.certificate r.stage.inclusion r.stage.inclusion_lang
  refine ⟨⟨e,he,hfix,?_⟩⟩
  intro p
  obtain ⟨s₀,hs,hpoint⟩ := r.extends_original p
  have hp : ∀ a ∈ p.point.source, s₀ (r.stage.inclusion a) = r.stage.inclusion (p.point a) := by
    intro a ha
    simpa only [r.stage.inclusion_apply] using hpoint a ha
  obtain ⟨C,hC,hzero⟩ := zeroRow_request_extension S H R B hB Δ A hA r.stage.model hL
    r.stage.inclusion p s₀ hp
  refine ⟨decodedLiftAut S H R B hB Δ hΔ A hA r.stage.model hL r.certificate s₀ C hC,hs,?_⟩
  intro a ha
  exact hzero a ha
end
end CCO.FullRows
