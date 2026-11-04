import CCO.TypedOrbitFrames.ChordImageSAP
import CCO.FiniteHelpers

/-!
# B053 C03: the genuine complete two-vertex OLD chord base

Two old homomorphic cycle images that agree on a specified typed
diversity atom have isomorphic complete induced TWO-POINT substructures.
An actual old automorphism aligns their endpoints at once.

This constructs the required two induced base embeddings into the actual
OLD image objects, without treating a possibly noninjective formal cycle
itself as an age object. With ChordImageSAP, this supplies the old SAP
image-gluing operation. The separate final induction must still
identify the two smaller cycle diagrams with the original split cycle.
-/

universe u v w t

namespace CCO.TypedOrbitFrames

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ i : ι, MulAction G (X i)]

/-- The COMPLETE literal finite old induced chord pair. Its two
vertices are actual tagged original points; the full old colour
on the pair (including the converse and real diagonal) is inherited. -/
def originalOldChordPair {i j : ι} (x : X i) (y : X j) :
    FiniteInduced (X := X) where
  vertices := { (⟨i,x⟩ : Sigma X), (⟨j,y⟩ : Sigma X) }
  finite_vertices := Set.finite_pair _ _

/-- A genuine original-group element restricting to an old finite
induced C has an induced image embedding into any finite old A
containing its full moved image. This uses ONE canonical old group
action on Sigma X; sort and all old pair colours are preserved. -/
def originalGroupFiniteInducedEmbedding
    (H : HomogeneousSource S G)
    (g : G) (C A : FiniteInduced (X := X))
    (hImage : ∀ p : ↥C.vertices, g • p.val ∈ A.vertices) :
    InducedEmbedding S C A where
  toEmbedding := {
    toFun := fun p => ⟨g • p.val, hImage p⟩
    inj' := by
      intro p q heq
      apply Subtype.ext
      have h : g • p.val = g • q.val :=
        congrArg Subtype.val heq
      have hi := congrArg (fun z : Sigma X => g⁻¹ • z) h
      simpa only [inv_smul_smul] using hi
  }
  preserves_sort := by
    intro p
    exact H.preserves_sort g p.val
  preserves_colours := by
    intro p q
    exact (H.preserves_colours g p.val q.val).symm

/-- Source11 C03: from two actual images of the SAME old fine
diversity chord, construct the common COMPLETE two-point base
and both genuine induced-AGE embeddings into the original image
structures. The second embedding uses ONE old automorphism moving
both endpoints. There is no quotient-age or hidden SAP here. -/
theorem original_old_chord_pair_actual_image_embeddings
    (H : HomogeneousSource S G)
    {i j : ι} (a : S.Atom i j)
    (x x' : X i) (y y' : X j)
    (hxy : S.colour x y = some a)
    (hx'y' : S.colour x' y' = some a)
    (A B : FiniteInduced (X := X))
    (hxA : (⟨i,x⟩ : Sigma X) ∈ A.vertices)
    (hyA : (⟨j,y⟩ : Sigma X) ∈ A.vertices)
    (hxB : (⟨i,x'⟩ : Sigma X) ∈ B.vertices)
    (hyB : (⟨j,y'⟩ : Sigma X) ∈ B.vertices) :
    ∃ (C : FiniteInduced (X := X))
      (eCA : InducedEmbedding S C A)
      (eCB : InducedEmbedding S C B)
      (c₀ c₁ : ↥C.vertices),
      c₀ ≠ c₁ ∧
      (eCA.toEmbedding c₀).val = (⟨i,x⟩ : Sigma X) ∧
      (eCA.toEmbedding c₁).val = (⟨j,y⟩ : Sigma X) ∧
      (eCB.toEmbedding c₀).val = (⟨i,x'⟩ : Sigma X) ∧
      (eCB.toEmbedding c₁).val = (⟨j,y'⟩ : Sigma X) := by
  classical
  obtain ⟨g,hgx,hgy⟩ :=
    align_actual_typed_chord_pair S H a x x' y y' hxy hx'y'
  let C : FiniteInduced (X := X) := originalOldChordPair x y
  have hCsub : C.vertices ⊆ A.vertices := by
    intro z hz
    have hz' :
        z = (⟨i,x⟩ : Sigma X) ∨ z = (⟨j,y⟩ : Sigma X) := by
      simpa only [C, originalOldChordPair, Set.mem_insert_iff,
        Set.mem_singleton_iff] using hz
    rcases hz' with h | h
    · simpa only [h] using hxA
    · simpa only [h] using hyA
  have hCmove : ∀ p : ↥C.vertices, g • p.val ∈ B.vertices := by
    intro p
    have hp : p.val = (⟨i,x⟩ : Sigma X) ∨
        p.val = (⟨j,y⟩ : Sigma X) := by
      simpa only [C, originalOldChordPair, Set.mem_insert_iff,
        Set.mem_singleton_iff] using p.property
    rcases hp with h | h
    · rw [h]
      simpa only [Sigma.smul_mk, hgx] using hxB
    · rw [h]
      simpa only [Sigma.smul_mk, hgy] using hyB
  let eCA := inducedInclusion S C A hCsub
  let eCB := originalGroupFiniteInducedEmbedding S H g C B hCmove
  have hc₀ : (⟨i,x⟩ : Sigma X) ∈ C.vertices := by
    simp [C, originalOldChordPair]
  have hc₁ : (⟨j,y⟩ : Sigma X) ∈ C.vertices := by
    simp [C, originalOldChordPair]
  let c₀ : ↥C.vertices := ⟨⟨i,x⟩,hc₀⟩
  let c₁ : ↥C.vertices := ⟨⟨j,y⟩,hc₁⟩
  have hdiff : c₀ ≠ c₁ := by
    intro h
    exact S.atomRel_ne hxy (congrArg Subtype.val h)
  refine ⟨C,eCA,eCB,c₀,c₁,hdiff,?_,?_,?_,?_⟩
  · rfl
  · rfl
  · change g • (⟨i,x⟩ : Sigma X) = ⟨i,x'⟩
    simp only [Sigma.smul_mk, hgx]
  · change g • (⟨j,y⟩ : Sigma X) = ⟨j,y'⟩
    simp only [Sigma.smul_mk, hgy]

end CCO.TypedOrbitFrames
