import CCO.FullRows.Consumer

/-! The actual decoded language component is recoverable ONTO THE
underlying permutation IMAGE, provided the stipulated source has full
owner support. Surjectivity uses ALL empty requests on the SAME decoder. -/
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
local notation "W₀" => encode (decodedData S H R B hB Δ hΔ A hA E hLocal c)

theorem sourceTag_injective : Function.Injective tags := by
  intro a b he
  exact Subtype.ext (Subtype.ext he)

def decodedPairGroup : Subgroup ((tags).range × Equiv.Perm (Vertex I K)) :=
  Semilinear.pairGroup (tags).range (vertexOwner S H R B hB Δ A hA E hLocal)
    (decodedColour S H R B hB Δ hΔ A hA E hLocal c)

def decodedPermutationImage : Subgroup (Equiv.Perm (Vertex I K)) :=
  (Semilinear.forget (tags).range (decodedPairGroup S H R B hB Δ hΔ A hA E hLocal c)).range

/-- An actual decoded full-language automorphism supplies a genuine
semilinear pair. Original equality is recovered without adding an atom. -/
def decodedAutPair (g : Structure.Automorphism act W₀) :
    decodedPairGroup S H R B hB Δ hΔ A hA E hLocal c := by
  let f := exactMapOfEmbedding tags (automorphismEmbedding tags g)
  refine ⟨(⟨tags g.lang,⟨g.lang,rfl⟩⟩,automorphismPerm tags g),f.owner,?_⟩
  intro x y
  have hf (a : S.Atom () ()) :
      decodedColour S H R B hB Δ hΔ A hA E hLocal c (g x) (g y) = some a ↔
      decodedColour S H R B hB Δ hΔ A hA E hLocal c x y = some a := f.fine a x y
  cases hd : decodedColour S H R B hB Δ hΔ A hA E hLocal c x y with
  | none =>
    cases hi : decodedColour S H R B hB Δ hΔ A hA E hLocal c (g x) (g y) with
    | none => exact hi
    | some a => have hh := (hf a).mp hi; rw [hd] at hh; cases hh
  | some a => exact (hf a).mpr hd

variable (j : Structure.Embedding act (encode D₀) E) (hj : j.lang=1)
variable (hsupport : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b)

def decodedForgetIso (j : Structure.Embedding act (encode D₀) E) (hj : j.lang=1)
    (hsupport : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b) :
    decodedPairGroup S H R B hB Δ hΔ A hA E hLocal c ≃*
      decodedPermutationImage S H R B hB Δ hΔ A hA E hLocal c :=
  Semilinear.forgetIso (vertexOwner S H R B hB Δ A hA E hLocal)
    (vertexOwner_surjective_of_source S H R B hB Δ A hA E hLocal j hj hsupport)
    (decodedPairGroup S H R B hB Δ hΔ A hA E hLocal c)
    (Semilinear.pairGroup_owner (tags).range _ _)

/-- The component on the ACTUAL underlying permutation image is a group
homomorphism. It is not a homomorphic section of a quotient map. -/
def decodedOwnerComponent (j : Structure.Embedding act (encode D₀) E) (hj : j.lang=1)
    (hsupport : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b) :
    decodedPermutationImage S H R B hB Δ hΔ A hA E hLocal c →* Δ :=
  (MonoidHom.ofInjective (sourceTag_injective S H R B Δ)).symm.toMonoidHom.comp
    (Semilinear.languageOnImage (vertexOwner S H R B hB Δ A hA E hLocal)
      (vertexOwner_surjective_of_source S H R B hB Δ A hA E hLocal j hj hsupport)
      (decodedPairGroup S H R B hB Δ hΔ A hA E hLocal c)
      (Semilinear.pairGroup_owner (tags).range _ _))

theorem RowOutput.pair_language_surjective
    (j : Structure.Embedding act (encode D₀) E) (hj : j.lang=1)
    (r : RowOutput S H R B hB Δ hΔ A hA E hLocal c j hj) :
    Function.Surjective (Semilinear.language (tags).range (decodedPairGroup S H R B hB Δ hΔ A hA E hLocal c)) := by
  intro γ
  obtain ⟨δ,hδ⟩ := γ.property
  obtain ⟨g,hg⟩ := RowOutput.every_language S H R B hB Δ hΔ A hA E hLocal c j hj r δ
  refine ⟨decodedAutPair S H R B hB Δ hΔ A hA E hLocal c g,?_⟩
  apply Subtype.ext
  exact (congrArg tags hg).trans hδ

theorem RowOutput.ownerComponent_surjective
    (j : Structure.Embedding act (encode D₀) E) (hj : j.lang=1)
    (hsupport : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b)
    (r : RowOutput S H R B hB Δ hΔ A hA E hLocal c j hj) :
    Function.Surjective (decodedOwnerComponent S H R B hB Δ hΔ A hA E hLocal c j hj hsupport) := by
  apply (MonoidHom.ofInjective (sourceTag_injective S H R B Δ)).symm.surjective.comp
  exact Semilinear.languageOnImage_surjective (vertexOwner S H R B hB Δ A hA E hLocal)
    (vertexOwner_surjective_of_source S H R B hB Δ A hA E hLocal j hj hsupport)
    (decodedPairGroup S H R B hB Δ hΔ A hA E hLocal c)
    (Semilinear.pairGroup_owner (tags).range _ _)
    (RowOutput.pair_language_surjective S H R B hB Δ hΔ A hA E hLocal c j hj r)

omit [Finite Z] in
/-- C32 with ACTUAL providers discharged. Full support is explicitly
checked on the original complete source, before any independent orbit trim. -/
theorem full_support_relative_witness [Finite A] (hne : A.Nonempty)
    (hfull : ∀ b : ↥B, ∃ a : A, (sourceData S H R B hB).owner a.val = b) :
    ∃ r : CompletableReservoir S H R B hB Δ A hA (reservoirThreshold S H R B),
      letI := r.stage.finiteNew
      ∃ out : RowOutput S H R B hB Δ hΔ A hA r.stage.model
        (locallyInSource_of_faithful tags r.stage.inclusion r.stage.faithful)
        r.certificate r.stage.inclusion r.stage.inclusion_lang,
      Function.Surjective (decodedOwnerComponent S H R B hB Δ hΔ A hA r.stage.model
        (locallyInSource_of_faithful tags r.stage.inclusion r.stage.faithful)
        r.certificate r.stage.inclusion r.stage.inclusion_lang hfull) := by
  obtain ⟨r,hr⟩ := actual_relative_witness S H R B hB Δ hΔ A hA hne
  refine ⟨r,?_⟩
  letI := r.stage.finiteNew
  obtain ⟨out⟩ := hr
  exact ⟨out,RowOutput.ownerComponent_surjective S H R B hB Δ hΔ A hA r.stage.model
    (locallyInSource_of_faithful tags r.stage.inclusion r.stage.faithful)
    r.certificate r.stage.inclusion r.stage.inclusion_lang hfull out⟩
end
end CCO.FullRows
