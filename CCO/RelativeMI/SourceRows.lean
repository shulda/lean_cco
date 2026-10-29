import CCO.RelativeMI.RecordedDecoder
import CCO.FullRows.SourceRows
import CCO.HKNReservoir.FinalAlignment

/-! The literal zero-row source is induced in the ONE decoder. Full owner
support comes from the original source before any orbit trim. One global
named automorphism then aligns the entire original source simultaneously. -/
universe v w t y
namespace CCO.RelativeMI
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings FullRows
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
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "tag" => sourceTag S H R B Δ
local notation "act" => sourceAction S H R B Δ
local notation "coords" => reservoirCoordinates S H R B hB Δ A hA E hLocal

/-- Every old source fine atom is retained: either inside its actual
packet, or in a complete recorded matrix between source packets. -/
theorem zeroRow_decoded_fine (j : Structure.Embedding act (encode D₀) E)
    (a b : A) (d : S.Atom () ()) (hd : (sourceData S H R B hB).fine d a.val b.val) :
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c
      (zeroRowEmbed S H R B hB Δ A hA E hLocal j a)
      (zeroRowEmbed S H R B hB Δ A hA E hLocal j b) = some d := by
  have hf := (embedding_fine_iff tag j d a b).mpr hd
  apply decodedColour_sparse_record S H R B hB Δ readingData hΔ A hA E hLocal c
  · by_cases hab : (coords (j a)).1 = (coords (j b)).1
    · exact Or.inl (Prod.ext hab rfl)
    · exact Or.inr (sourceIndices_recorded S H R B hB Δ A hA E hLocal j
        _ ⟨a,rfl⟩ _ ⟨b,rfl⟩ hab)
  · simpa only [zeroRowEmbed_projection,Equiv.symm_apply_apply] using hf

/-- All optional original colours are retained, including equality. -/
theorem zeroRow_decoded_colours (j : Structure.Embedding act (encode D₀) E) :
    ∀ a b : A,
      col S (decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c
        (zeroRowEmbed S H R B hB Δ A hA E hLocal j a)).val
        (decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c
          (zeroRowEmbed S H R B hB Δ A hA E hLocal j b)).val =
      col S a.val.down.val b.val.down.val := by
  letI : Finite A := Finite.of_injective j.toFun j.injective
  apply source_base_colours_of_fine S H R B hB A
    (zeroRowEmbed S H R B hB Δ A hA E hLocal j)
    (decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c)
  intro a b d hd
  exact (decodedPoint_colour S H R B hB Δ readingData hΔ A hA E hLocal c _ _).trans
    (zeroRow_decoded_fine S H R B hB Δ readingData hΔ A hA E hLocal c j a b d hd)

/-- ONE named automorphism aligns ALL old source points at once. -/
theorem align_decoded_source (j : Structure.Embedding act (encode D₀) E)
    (hj : j.lang = 1) :
    ∃ k : NamedAut S H R B, ∀ a : A,
      k.val (decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c
        (zeroRowEmbed S H R B hB Δ A hA E hLocal j a)) = a.val.down := by
  letI : Finite A := Finite.of_injective j.toFun j.injective
  apply align_source_base S H R B hB A
    (zeroRowEmbed S H R B hB Δ A hA E hLocal j)
    (decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c)
  · intro a
    exact (decodedPoint_owner S H R B hB Δ readingData hΔ A hA E hLocal c _).trans
      (zeroRowEmbed_owner S H R B hB Δ A hA E hLocal j hj a)
  · exact zeroRow_decoded_colours S H R B hB Δ readingData hΔ A hA E hLocal c j

/-- Alignment only postcomposes the age certificate. The decoded full
colouring, literal owners and all named translations stay fixed. -/
theorem alignedDecodedPoint (j : Structure.Embedding act (encode D₀) E)
    (hj : j.lang = 1) :
    letI := TransversalPure.thinCommGroup S H R
    ∃ q : Vertex I K → NamedCarrier S H R B,
      Function.Injective q ∧
      (∀ x, ownerLabel S H R B (q x) = vertexOwner S H R B hB Δ A hA E hLocal x) ∧
      (∀ x y, col S (q x).val (q y).val =
        decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y) ∧
      (∀ g x, q (translate g x) = packetPoint S H R B hB g (q x)) ∧
      ∀ a : A, q (zeroRowEmbed S H R B hB Δ A hA E hLocal j a) = a.val.down := by
  letI := TransversalPure.thinCommGroup S H R
  obtain ⟨k,hk⟩ := align_decoded_source S H R B hB Δ readingData hΔ A hA E hLocal c j hj
  let q := decodedPoint S H R B hB Δ readingData hΔ A hA E hLocal c
  refine ⟨alignedMap S H R B k q,
    alignedMap_injective S H R B k q
      (decodedPoint_injective S H R B hB Δ readingData hΔ A hA E hLocal c),?_,?_,?_,hk⟩
  · intro x
    exact (alignedMap_owner S H R B k q x).trans
      (decodedPoint_owner S H R B hB Δ readingData hΔ A hA E hLocal c x)
  · intro x y
    exact (alignedMap_colours S H R B k q x y).trans
      (decodedPoint_colour S H R B hB Δ readingData hΔ A hA E hLocal c x y)
  · exact alignedMap_move S H R B hB k q translate
      (decodedPoint_translate S H R B hB Δ readingData hΔ A hA E hLocal c)
end
end CCO.RelativeMI
