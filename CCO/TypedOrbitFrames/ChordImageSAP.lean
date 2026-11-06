import CCO.TypedOrbitFrames.ChordPairAlignment
import CCO.SAPHelpers
import CCO.FiniteHelpers

/-!
# B053 C03: SAP gluing of ACTUAL finite induced OLD image structures

A homomorphism of a partial old-coloured diagram need not be
injective away from its specified diversity edges. We therefore
DO NOT apply AgeSAP to the formal partial cycles themselves.

Instead the image of any finite diagram homomorphism is a FINITE
INDUCED actual old-age object. Given embeddings of the same
complete old chord base into two such induced images, old AgeSAP
strongly amalgamates the ACTUAL images over precisely that base.
Images of all originally specified old edges retain their exact
typed optional colours, and any equality across the two amalgam
images must come from the shared old base. This is the correct
image-level gluing API consumed by the later chord-split induction.

Constructing the particular chord embeddings from a pair of
cycle homomorphisms and threading their vertex maps through the
split cycle is a separate remaining T01 step; the caller may not
simply assume the formal cycle is an induced-age object.
-/

universe u v w z t
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The ENTIRE actual finite old induced IMAGE of a homomorphism
of an arbitrary partial labelled old diagram. The map need not
be injective, but the image is a genuine finite induced age object. -/
def originalHomFiniteInducedImage
    {V : Type z} (D : PartialDiagram S V)
    (f : DiagramHom D) : FiniteInduced (X := X) := by
  letI : Finite V := D.finite_type
  refine ⟨Set.range f.image, ?_⟩
  simpa only [Set.image_univ] using
    ((Set.finite_univ : (Set.univ : Set V).Finite).image f.image)

/-- Every formal vertex belongs to the actual old induced image.
No injectivity of the formal diagram homomorphism is used. -/
theorem original_hom_mem_finite_induced_image
    {V : Type z} (D : PartialDiagram S V)
    (f : DiagramHom D) (v : V) :
    f.image v ∈ (originalHomFiniteInducedImage S D f).vertices := by
  exact ⟨v, rfl⟩

/-- Actual original SAP glues two genuine finite induced OLD image
objects over a common COMPLETE induced base. Every cross-factor
collision is forced by that very base, and all old typed optional
pair colours inside either original factor are reflected exactly.

There is NO application of SAP to a noninjective source cycle.
The maps of arbitrary formal source vertices pass to the actual
target only through their genuine induced image factors. -/
theorem original_induced_hom_images_sap_glue
    {V : Type z} {W : Type t}
    (L : PartialDiagram S V)
    (R : PartialDiagram S W)
    (f : DiagramHom L) (g : DiagramHom R)
    (sap : AgeSAP S)
    (C A B : FiniteInduced (X := X))
    (eCA : InducedEmbedding S C A)
    (eCB : InducedEmbedding S C B)
    (hA : ∀ v : V, f.image v ∈ A.vertices)
    (hB : ∀ w : W, g.image w ∈ B.vertices) :
    ∃ (M : FiniteInduced (X := X))
      (eAM : InducedEmbedding S A M)
      (eBM : InducedEmbedding S B M),
      (∀ c : ↥C.vertices,
        eAM.toEmbedding (eCA.toEmbedding c) =
          eBM.toEmbedding (eCB.toEmbedding c)) ∧
      (∀ v : V, ∀ w : W,
        eAM.toEmbedding ⟨f.image v, hA v⟩ =
          eBM.toEmbedding ⟨g.image w, hB w⟩ →
        ∃ c : ↥C.vertices,
          f.image v = (eCA.toEmbedding c).val ∧
          g.image w = (eCB.toEmbedding c).val) ∧
      (∀ v v' : V,
        taggedColour S
          (eAM.toEmbedding ⟨f.image v, hA v⟩).val
          (eAM.toEmbedding ⟨f.image v', hA v'⟩).val =
        taggedColour S (f.image v) (f.image v')) ∧
      (∀ w w' : W,
        taggedColour S
          (eBM.toEmbedding ⟨g.image w, hB w⟩).val
          (eBM.toEmbedding ⟨g.image w', hB w'⟩).val =
        taggedColour S (g.image w) (g.image w')) := by
  obtain ⟨M, eAM, eBM, hComm, hExact⟩ :=
    AgeSAP.amalgamate_exact_overlap S sap C A B eCA eCB
  refine ⟨M, eAM, eBM, hComm, ?_, ?_, ?_⟩
  · intro v w heq
    obtain ⟨c, hcA, hcB⟩ :=
      (hExact ⟨f.image v, hA v⟩ ⟨g.image w, hB w⟩).mp heq
    exact ⟨c, congrArg Subtype.val hcA.symm,
      congrArg Subtype.val hcB.symm⟩
  · intro v v'
    exact (eAM.preserves_colours
      ⟨f.image v, hA v⟩
      ⟨f.image v', hA v'⟩).symm
  · intro w w'
    exact (eBM.preserves_colours
      ⟨g.image w, hB w⟩
      ⟨g.image w', hB w'⟩).symm

end CCO.TypedOrbitFrames
