import CCO.RelativeMI.LocalWitness
import CCO.RelativeMI.OwnerLanguage

/-! Actual real readout of ONE aligned decoder, and the action of its
semilinear permutation IMAGE. The thin action gives a homomorphism into
this image; no section of an owner quotient is chosen. -/
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
local notation "tags" => sourceTag S H R B Δ
local notation "act" => sourceAction S H R B Δ
local notation "D₀" => finiteSourceData S H R B hB A hA
local notation "W₀" => encode (decodedData S H R B hB Δ readingData hΔ A hA E hLocal c)
local notation "L₀" => decodedPairGroup S H R B hB Δ readingData hΔ A hA E hLocal c
local notation "K₀" => decodedPermutationImage S H R B hB Δ readingData hΔ A hA E hLocal c

namespace DecoderOutput

variable {S H R B hB Δ readingData hΔ A hA E hLocal c}

/-- Forget only the auxiliary owner membership and universe lift, while
retaining the injective ACTUAL real realization. -/
def realEmbedding {j : Structure.Embedding act (encode D₀) E} {hj : j.lang = 1}
    (out : DecoderOutput S H R B hB Δ readingData hΔ A hA E hLocal c j hj) : Vertex I K ↪ M where
  toFun x := (out.embedding x).down.val
  inj' := by
    intro x y he
    apply out.embedding.injective
    exact ULift.ext _ _ (Subtype.ext he)

theorem realEmbedding_ownerLabel {j : Structure.Embedding act (encode D₀) E} {hj : j.lang = 1}
    (out : DecoderOutput S H R B hB Δ readingData hΔ A hA E hLocal c j hj) (x : Vertex I K) :
    ownerLabel S H R B (out.embedding x).down = vertexOwner S H R B hB Δ A hA E hLocal x := by
  have ho := (exactMapOfEmbedding tags out.embedding).owner x
  change ownerLabel S H R B (out.embedding x).down =
    tags out.embedding.lang (vertexOwner S H R B hB Δ A hA E hLocal x) at ho
  simpa only [out.embedding_lang,map_one,Equiv.Perm.one_apply] using ho

theorem realEmbedding_owner {j : Structure.Embedding act (encode D₀) E} {hj : j.lang = 1}
    (out : DecoderOutput S H R B hB Δ readingData hΔ A hA E hLocal c j hj) (x : Vertex I K) :
    owner S H R (out.realEmbedding x) = (vertexOwner S H R B hB Δ A hA E hLocal x).val :=
  congrArg Subtype.val (out.realEmbedding_ownerLabel x)

theorem realEmbedding_colour {j : Structure.Embedding act (encode D₀) E} {hj : j.lang = 1}
    (out : DecoderOutput S H R B hB Δ readingData hΔ A hA E hLocal c j hj) (x y : Vertex I K) :
    col S (out.realEmbedding x) (out.realEmbedding y) =
      decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y := by
  let f := exactMapOfEmbedding tags out.embedding
  cases hd : decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y with
  | none =>
    have hxy := (decodedColour_none S H R B hB Δ readingData hΔ A hA E hLocal c x y).mp hd
    subst y
    exact (col_none S _ _).mpr rfl
  | some a => exact (f.fine a x y).mpr hd

theorem realEmbedding_translate {j : Structure.Embedding act (encode D₀) E} {hj : j.lang = 1}
    (out : DecoderOutput S H R B hB Δ readingData hΔ A hA E hLocal c j hj) (g : K) (x : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    out.realEmbedding (translate g x) = g.val (out.realEmbedding x) := by
  letI := TransversalPure.thinCommGroup S H R
  have hm := (exactMapOfEmbedding tags out.embedding).move g x
  exact congrArg (fun z : SourceCarrier S H R B => z.down.val) hm

theorem realEmbedding_source_fixed {j : Structure.Embedding act (encode D₀) E} {hj : j.lang = 1}
    (out : DecoderOutput S H R B hB Δ readingData hΔ A hA E hLocal c j hj) (a : A) :
    out.realEmbedding (zeroRowEmbed S H R B hB Δ A hA E hLocal j a) = a.val.down.val :=
  congrArg (fun z : SourceCarrier S H R B => z.down.val) (out.source_fixed a)
end DecoderOutput

/-- The actual global thin permutations lie in the underlying IMAGE of
the semilinear group. This homomorphism uses no owner-action faithfulness. -/
def decodedThinImageHom : K →* K₀ where
  toFun g := ⟨decodedThinPerm S H R B E g,by
    refine ⟨decodedAutPair S H R B hB Δ readingData hΔ A hA E hLocal c
      (decodedThinAut S H R B hB Δ readingData hΔ A hA E hLocal c g),?_⟩
    apply Equiv.ext
    intro x
    rfl⟩
  map_one' := by
    apply Subtype.ext
    exact (decodedThinPerm S H R B E).map_one
  map_mul' g h := by
    apply Subtype.ext
    exact (decodedThinPerm S H R B E).map_mul g h

@[simp] theorem decodedThinImageHom_apply (g : K) (x : Vertex I K) :
    letI := TransversalPure.thinCommGroup S H R
    (decodedThinImageHom S H R B hB Δ readingData hΔ A hA E hLocal c g).val x = translate g x := rfl

/-- The recovered component is the literal first component of the unique
semilinear pair above the image permutation. Full support is checked here. -/
theorem decodedOwnerComponent_tag (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1)
    (hsupport : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b) (g : K₀) :
    tags (decodedOwnerComponent S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport g) =
      ((decodedForgetIso S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport).symm g).val.1.val := by
  let e := MonoidHom.ofInjective (FullRows.sourceTag_injective S H R B Δ)
  have he := e.apply_symm_apply (Semilinear.languageOnImage
    (vertexOwner S H R B hB Δ A hA E hLocal)
    (vertexOwner_surjective_of_source S H R B hB Δ A hA E hLocal j hj hsupport)
    L₀ (Semilinear.pairGroup_owner (tags).range _ _) g)
  exact congrArg Subtype.val he

theorem decodedImage_owner (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1)
    (hsupport : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b)
    (g : K₀) (x : Vertex I K) :
    vertexOwner S H R B hB Δ A hA E hLocal (g.val x) =
      tags (decodedOwnerComponent S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport g)
        (vertexOwner S H R B hB Δ A hA E hLocal x) := by
  let e := decodedForgetIso S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport
  let p := e.symm g
  have hp : p.val.2 = g.val := congrArg Subtype.val (e.apply_symm_apply g)
  rw [decodedOwnerComponent_tag S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport]
  rw [← hp]
  exact Semilinear.pairGroup_owner (tags).range
    (vertexOwner S H R B hB Δ A hA E hLocal)
    (decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c) p x

theorem decodedImage_colour (g : K₀) (x y : Vertex I K) :
    decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c (g.val x) (g.val y) =
      decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c x y := by
  obtain ⟨p,hp⟩ := g.property
  have hc := Semilinear.pairGroup_colour (tags).range
    (vertexOwner S H R B hB Δ A hA E hLocal)
    (decodedColour S H R B hB Δ readingData hΔ A hA E hLocal c) p x y
  change p.val.2 = g.val at hp
  rw [hp] at hc
  exact hc

theorem DecoderOutput.realEmbedding_image_colour
    (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1)
    (out : DecoderOutput S H R B hB Δ readingData hΔ A hA E hLocal c j hj)
    (g : K₀) (x y : Vertex I K) :
    col S (out.realEmbedding (g.val x)) (out.realEmbedding (g.val y)) =
      col S (out.realEmbedding x) (out.realEmbedding y) :=
  (out.realEmbedding_colour _ _).trans
    ((decodedImage_colour S H R B hB Δ readingData hΔ A hA E hLocal c g x y).trans
      (out.realEmbedding_colour x y).symm)

/-- An actual decoded automorphism determines a point of the underlying
permutation IMAGE, retaining its exact action on every vertex. -/
def decodedAutImage (g : Structure.Automorphism act W₀) : K₀ :=
  ⟨automorphismPerm tags g,⟨decodedAutPair S H R B hB Δ readingData hΔ A hA E hLocal c g,rfl⟩⟩

@[simp] theorem decodedAutImage_apply (g : Structure.Automorphism act W₀) (x : Vertex I K) :
    (decodedAutImage S H R B hB Δ readingData hΔ A hA E hLocal c g).val x = g x := rfl

/-- Full source support recovers the ENTIRE given language component of
each actual automorphism, including an empty-real-domain extension. -/
theorem decodedOwnerComponent_autImage
    (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1)
    (hsupport : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b)
    (g : Structure.Automorphism act W₀) :
    decodedOwnerComponent S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport
      (decodedAutImage S H R B hB Δ readingData hΔ A hA E hLocal c g) = g.lang := by
  apply FullRows.sourceTag_injective S H R B Δ
  apply Equiv.ext
  intro b
  obtain ⟨a,ha⟩ := hsupport b
  let x := zeroRowEmbed S H R B hB Δ A hA E hLocal j a
  have hx : vertexOwner S H R B hB Δ A hA E hLocal x = b :=
    (zeroRowEmbed_owner S H R B hB Δ A hA E hLocal j hj a).trans ha
  have ho := decodedImage_owner S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport
    (decodedAutImage S H R B hB Δ readingData hΔ A hA E hLocal c g) x
  have hg := (exactMapOfEmbedding tags (automorphismEmbedding tags g)).owner x
  change vertexOwner S H R B hB Δ A hA E hLocal (g x) =
    tags g.lang (vertexOwner S H R B hB Δ A hA E hLocal x) at hg
  change vertexOwner S H R B hB Δ A hA E hLocal (g x) =
    tags (decodedOwnerComponent S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport
      (decodedAutImage S H R B hB Δ readingData hΔ A hA E hLocal c g))
      (vertexOwner S H R B hB Δ A hA E hLocal x) at ho
  rw [hx] at ho hg
  exact ho.symm.trans hg

theorem decodedOwnerComponent_thinImage
    (j : Structure.Embedding act (encode D₀) E) (hj : j.lang = 1)
    (hsupport : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b) (g : K) :
    decodedOwnerComponent S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport
      (decodedThinImageHom S H R B hB Δ readingData hΔ A hA E hLocal c g) =
      decodedThinOwnerHom S H R B hB Δ hΔ g := by
  have he : decodedThinImageHom S H R B hB Δ readingData hΔ A hA E hLocal c g =
      decodedAutImage S H R B hB Δ readingData hΔ A hA E hLocal c
        (decodedThinAut S H R B hB Δ readingData hΔ A hA E hLocal c g) := by
    apply Subtype.ext
    apply Equiv.ext
    intro x
    rfl
  rw [he,decodedOwnerComponent_autImage S H R B hB Δ readingData hΔ A hA E hLocal c j hj hsupport]
  rfl
end
end CCO.RelativeMI
