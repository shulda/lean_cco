import CCO.FullRows.SourceRows

/-! The fixed literal decoder as an actual complete original-language
structure. Its age embedding and its aligned embedding certify the SAME
table, without making the completion certificate equivariant. -/
universe v w t y
namespace CCO.FullRows
noncomputable section
open AllThoseEPPA HKNReservoir ParityHasse.Original RealHull.Geometry RealClosure.Bounds
open FinitePackets.Normalization OwnerTransversal TransversalAge SafeReadings
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
local notation "tags" => sourceTag S H R B Δ
local notation "act" => sourceAction S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA

/-- ONE literal complete table, fixed before selecting any structural
automorphism or legal row correction. -/
def decodedData : Data ↥B K (S.Atom () ()) (Vertex I K) := by
  letI := TransversalPure.thinCommGroup S H R
  exact {
    owner := vertexOwner S H R B hB Δ A hA E hLocal
    fine := fun a x y => decodedColour S H R B hB Δ hΔ A hA E hLocal c x y = some a
    move := translate }

/-- Exact age membership includes reflection of every fine relation and
equality of the whole singleton named-function values. -/
def decodedEmbedding :
    Structure.Embedding act (encode (decodedData S H R B hB Δ hΔ A hA E hLocal c))
      (sourceStructure S H R B hB) := by
  letI := TransversalPure.thinCommGroup S H R
  let q := decodedPoint S H R B hB Δ hΔ A hA E hLocal c
  refine (ExactMap.mk (tag := tags)
    (D := decodedData S H R B hB Δ hΔ A hA E hLocal c)
    (E := sourceData S H R B hB) 1 (fun x => ULift.up (q x))
    (fun _ _ he => decodedPoint_injective S H R B hB Δ hΔ A hA E hLocal c
      (congrArg ULift.down he)) ?_ ?_ ?_).toEmbedding
  · intro x
    exact decodedPoint_owner S H R B hB Δ hΔ A hA E hLocal c x
  · intro a x y
    exact Iff.of_eq (congrArg (· = some a)
      (decodedPoint_colour S H R B hB Δ hΔ A hA E hLocal c x y))
  · intro g x
    exact ULift.ext _ _ (decodedPoint_translate S H R B hB Δ hΔ A hA E hLocal c g x)

@[simp] theorem decodedEmbedding_lang :
    (decodedEmbedding S H R B hB Δ hΔ A hA E hLocal c).lang = 1 := rfl

@[simp] theorem decodedEmbedding_apply (x : Vertex I K) :
    decodedEmbedding S H R B hB Δ hΔ A hA E hLocal c x =
      ULift.up (decodedPoint S H R B hB Δ hΔ A hA E hLocal c x) := rfl

theorem decoded_fine_complete (x y : Vertex I K) (hxy : x ≠ y) :
    ∃ a, (decodedData S H R B hB Δ hΔ A hA E hLocal c).fine a x y := by
  obtain ⟨a,ha⟩ := source_fine_complete S H R B hB
    (fun he => hxy ((decodedEmbedding S H R B hB Δ hΔ A hA E hLocal c).injective he))
  exact ⟨a,((exactMapOfEmbedding tags
    (decodedEmbedding S H R B hB Δ hΔ A hA E hLocal c)).fine a x y).mp ha⟩

/-- The original source embeds exactly in the completed zero rows. -/
def sourceZeroEmbedding (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1) :
    Structure.Embedding act (encode D₀)
      (encode (decodedData S H R B hB Δ hΔ A hA E hLocal c)) := by
  letI := TransversalPure.thinCommGroup S H R
  refine (ExactMap.mk (tag := tags) (D := D₀)
    (E := decodedData S H R B hB Δ hΔ A hA E hLocal c) 1
    (zeroRowEmbed S H R B hB Δ A hA E hLocal j)
    (zeroRowEmbed_injective S H R B hB Δ A hA E hLocal j) ?_ ?_ ?_).toEmbedding
  · intro a
    exact zeroRowEmbed_owner S H R B hB Δ A hA E hLocal j hj a
  · intro d a b
    have hc := (decodedPoint_colour S H R B hB Δ hΔ A hA E hLocal c
      (zeroRowEmbed S H R B hB Δ A hA E hLocal j a)
      (zeroRowEmbed S H R B hB Δ A hA E hLocal j b)).symm.trans
      (zeroRow_decoded_colours S H R B hB Δ hΔ A hA E hLocal c j a b)
    exact Iff.of_eq (congrArg (· = some d) hc)
  · exact zeroRowEmbed_move S H R B hB Δ A hA E hLocal j

@[simp] theorem sourceZeroEmbedding_lang (j : Structure.Embedding act (encode D₀) E)
    (hj : j.lang = 1) :
    (sourceZeroEmbedding S H R B hB Δ hΔ A hA E hLocal c j hj).lang = 1 := rfl

@[simp] theorem sourceZeroEmbedding_apply (j : Structure.Embedding act (encode D₀) E)
    (hj : j.lang = 1) (a : A) :
    sourceZeroEmbedding S H R B hB Δ hΔ A hA E hLocal c j hj a =
      zeroRowEmbed S H R B hB Δ A hA E hLocal j a := rfl

/-- ONE exact actual-age embedding fixes ALL old source points. The
decoder table stays identical while its age certificate is aligned. -/
theorem alignedDecodedEmbedding (j : Structure.Embedding act (encode D₀) E)
    (hj : j.lang = 1) :
    ∃ e : Structure.Embedding act
      (encode (decodedData S H R B hB Δ hΔ A hA E hLocal c))
      (sourceStructure S H R B hB), e.lang = 1 ∧
      ∀ a : A, e (zeroRowEmbed S H R B hB Δ A hA E hLocal j a) = a.val := by
  letI := TransversalPure.thinCommGroup S H R
  obtain ⟨q,hq,ho,hc,hm,hfix⟩ :=
    alignedDecodedPoint S H R B hB Δ hΔ A hA E hLocal c j hj
  let e : ExactMap tags (decodedData S H R B hB Δ hΔ A hA E hLocal c)
      (sourceData S H R B hB) := {
    lang := 1
    toFun := fun x => ULift.up (q x)
    injective := fun _ _ he => hq (congrArg ULift.down he)
    owner := ho
    fine := fun a x y => Iff.of_eq (congrArg (· = some a) (hc x y))
    move := fun g x => ULift.ext _ _ (hm g x) }
  exact ⟨e.toEmbedding,rfl,fun a => ULift.ext _ _ (hfix a)⟩
end
end CCO.FullRows
