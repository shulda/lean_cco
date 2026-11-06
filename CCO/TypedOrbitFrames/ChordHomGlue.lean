import CCO.TypedOrbitFrames.ChordCompletePair

/-!
# B053 C03: glue the two genuinely realised OLD chord-cycle images

Given homomorphisms of two finite old partial diagrams, the designated
chord endpoints in both ACTUAL images carry the same old diversity
atom. Their actual induced image structures (NOT the formal cycles)
share a complete old two-point base via one original automorphism.
Old AgeSAP therefore produces a single real coloured target for both
maps, matching the two chord endpoints and preserving all specified
old typed colours in each image.

The homomorphism of a split *single* cycle then requires the source
combinatorial identification of the two subcycles along exactly the
two chord vertices. That is a separate remaining C04 consumer;
there is no assertion of a whole-graph CCO completion here.
-/

universe u v w t z p
namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- One ACTUAL original SAP amalgam for two finite OLD
homomorphism images whose two specified diversity-chord
endpoints have the same full old fine pair type.

No injectivity assumption on either formal source homomorphism
is made: only images are age objects, and the chord atom forces
the designated two endpoints to be distinct. -/
theorem original_same_chord_hom_images_sap_glue
    (H : HomogeneousSource S G) (sap : AgeSAP S)
    {V : Type z} {W : Type p}
    (L : PartialDiagram S V) (R : PartialDiagram S W)
    (f : DiagramHom L) (g : DiagramHom R)
    {i j : ι} (a : S.Atom i j)
    (x x' : X i) (y y' : X j)
    (hxy : S.colour x y = some a)
    (hx'y' : S.colour x' y' = some a)
    (u₀ u₁ : V) (v₀ v₁ : W)
    (hl₀ : f.image u₀ = (⟨i,x⟩ : Sigma X))
    (hl₁ : f.image u₁ = (⟨j,y⟩ : Sigma X))
    (hr₀ : g.image v₀ = (⟨i,x'⟩ : Sigma X))
    (hr₁ : g.image v₁ = (⟨j,y'⟩ : Sigma X)) :
    ∃ (M : FiniteInduced (X := X))
      (fl : V → Sigma X) (gr : W → Sigma X),
      (∀ u : V, fl u ∈ M.vertices) ∧
      (∀ v : W, gr v ∈ M.vertices) ∧
      (∀ u v : V,
        taggedColour S (fl u) (fl v) =
          taggedColour S (f.image u) (f.image v)) ∧
      (∀ u v : W,
        taggedColour S (gr u) (gr v) =
          taggedColour S (g.image u) (g.image v)) ∧
      fl u₀ = gr v₀ ∧ fl u₁ = gr v₁ := by
  let A : FiniteInduced (X := X) :=
    originalHomFiniteInducedImage S L f
  let B : FiniteInduced (X := X) :=
    originalHomFiniteInducedImage S R g
  have hA : ∀ u : V, f.image u ∈ A.vertices :=
    original_hom_mem_finite_induced_image S L f
  have hB : ∀ v : W, g.image v ∈ B.vertices :=
    original_hom_mem_finite_induced_image S R g
  have hxA : (⟨i,x⟩ : Sigma X) ∈ A.vertices := by
    rw [← hl₀]
    exact hA u₀
  have hyA : (⟨j,y⟩ : Sigma X) ∈ A.vertices := by
    rw [← hl₁]
    exact hA u₁
  have hxB : (⟨i,x'⟩ : Sigma X) ∈ B.vertices := by
    rw [← hr₀]
    exact hB v₀
  have hyB : (⟨j,y'⟩ : Sigma X) ∈ B.vertices := by
    rw [← hr₁]
    exact hB v₁
  obtain ⟨C,eCA,eCB,c₀,c₁,_,hA₀,hA₁,hB₀,hB₁⟩ :=
    original_old_chord_pair_actual_image_embeddings S H a
      x x' y y' hxy hx'y' A B hxA hyA hxB hyB
  obtain ⟨M,eAM,eBM,hCommon,_,hPresL,hPresR⟩ :=
    original_induced_hom_images_sap_glue
      S L R f g sap C A B eCA eCB hA hB
  refine ⟨M,
      (fun u : V => (eAM.toEmbedding ⟨f.image u,hA u⟩).val),
      (fun v : W => (eBM.toEmbedding ⟨g.image v,hB v⟩).val),
      ?_, ?_, hPresL, hPresR, ?_, ?_⟩
  · intro u
    exact (eAM.toEmbedding ⟨f.image u,hA u⟩).property
  · intro v
    exact (eBM.toEmbedding ⟨g.image v,hB v⟩).property
  · have hleft : (⟨f.image u₀,hA u₀⟩ : ↥A.vertices) =
        eCA.toEmbedding c₀ :=
      Subtype.ext (hl₀.trans hA₀.symm)
    have hright : (⟨g.image v₀,hB v₀⟩ : ↥B.vertices) =
        eCB.toEmbedding c₀ :=
      Subtype.ext (hr₀.trans hB₀.symm)
    calc
      (eAM.toEmbedding ⟨f.image u₀,hA u₀⟩).val =
          (eAM.toEmbedding (eCA.toEmbedding c₀)).val :=
        congrArg (fun z : ↥A.vertices => (eAM.toEmbedding z).val) hleft
      _ = (eBM.toEmbedding (eCB.toEmbedding c₀)).val :=
        congrArg Subtype.val (hCommon c₀)
      _ = (eBM.toEmbedding ⟨g.image v₀,hB v₀⟩).val :=
        congrArg (fun z : ↥B.vertices => (eBM.toEmbedding z).val) hright.symm
  · have hleft : (⟨f.image u₁,hA u₁⟩ : ↥A.vertices) =
        eCA.toEmbedding c₁ :=
      Subtype.ext (hl₁.trans hA₁.symm)
    have hright : (⟨g.image v₁,hB v₁⟩ : ↥B.vertices) =
        eCB.toEmbedding c₁ :=
      Subtype.ext (hr₁.trans hB₁.symm)
    calc
      (eAM.toEmbedding ⟨f.image u₁,hA u₁⟩).val =
          (eAM.toEmbedding (eCA.toEmbedding c₁)).val :=
        congrArg (fun z : ↥A.vertices => (eAM.toEmbedding z).val) hleft
      _ = (eBM.toEmbedding (eCB.toEmbedding c₁)).val :=
        congrArg Subtype.val (hCommon c₁)
      _ = (eBM.toEmbedding ⟨g.image v₁,hB v₁⟩).val :=
        congrArg (fun z : ↥B.vertices => (eBM.toEmbedding z).val) hright.symm

end CCO.TypedOrbitFrames
