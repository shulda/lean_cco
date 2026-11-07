import CCO.UnaryHN.TypedTransferBasis
import CCO.HiddenSAPReadings.SourceSupport

/-! The two genuine homomorphism-embedding interfaces test the SAME map.
Closed irreducible subsets and arbitrary irreducible embedded diagrams
agree by their actual induced closed images. Full unary-domain reflection
and all relation tuples, including nullary ones, are retained. -/

universe u v w t

namespace CCO.UnaryHN.Raw

/-- Forget only the irreducible-subobject clause, keeping the point map. -/
def HE.toHom {L : CCO.UnarySupport.Signature.{u}} {V W : Type v}
    {C : Typed L V} {D : Typed L W} {f : V → W} (h : HE C D f) :
    CCO.UnarySupport.Structure.Hom C D where
  point := f
  sort_eq := h.sort_eq
  map_func := h.map_func
  map_rel := h.map_rel

@[simp] theorem HE.toHom_point {L : CCO.UnarySupport.Signature.{u}} {V W : Type v}
    {C : Typed L V} {D : Typed L W} {f : V → W} (h : HE C D f) :
    h.toHom.point = f := rfl

end CCO.UnaryHN.Raw

namespace CCO.TerminalHiddenHN
open CCO.UnarySupport CCO.UnarySupport.Structure
open CCO.HiddenSAPReadings.SourceSupport
noncomputable section
variable {L : Signature.{u}}

/-- Pull back the actual closed factors and every displayed relation.
No totality or nonempty-carrier premise is needed. -/
def freeDecomposition_pullback {V : Type v} {W : Type w}
    {C : Structure L V} {D : Structure L W} (e : DiagramIso C D)
    (d : D.FreeDecomposition) : C.FreeDecomposition where
  left := e.equiv ⁻¹' d.left
  right := e.equiv ⁻¹' d.right
  left_closed F x hx y hy := d.left_closed F (e.equiv x) hx ((e.func_iff F x y).mpr hy)
  right_closed F x hx y hy := d.right_closed F (e.equiv x) hx ((e.func_iff F x y).mpr hy)
  cover := by
    apply Set.eq_univ_of_forall
    intro x
    have hx : e.equiv x ∈ d.left ∪ d.right := by rw [d.cover]; trivial
    exact hx
  left_proper := by
    intro h
    apply d.left_proper
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.equiv.symm y ∈ e.equiv ⁻¹' d.left := by rw [h]; trivial
    simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hy
  right_proper := by
    intro h
    apply d.right_proper
    apply Set.eq_univ_of_forall
    intro y
    have hy : e.equiv.symm y ∈ e.equiv ⁻¹' d.right := by rw [h]; trivial
    simpa only [Set.mem_preimage, Equiv.apply_symm_apply] using hy
  rel_local R xs hx := d.rel_local R (e.equiv ∘ xs) ((e.rel_iff R xs).mpr hx)

theorem irreducible_of_diagramIso {V : Type v} {W : Type w}
    {C : Structure L V} {D : Structure L W} (e : DiagramIso C D)
    (hC : C.Irreducible) : D.Irreducible := by
  constructor
  intro d
  exact hC.false (freeDecomposition_pullback e d)

/-- Every actual induced embedding carries irreducibility to its closed
image; this is proved by transport of free decompositions above. -/
theorem embedding_image_irreducible {V : Type v} {W : Type w}
    {C : Structure L V} {D : Structure L W} (e : Embedding C D)
    (hC : C.Irreducible) :
    (D.induce (Set.range e.point) (embedding_range_closed e)).Irreducible :=
  irreducible_of_diagramIso (embedding_image_iso e) hC

/-- Composition retains inducedness and reflects the full partial domain. -/
def embedding_comp {V : Type v} {W : Type w} {T : Type t}
    {C : Structure L V} {D : Structure L W} {A : Structure L T}
    (e : Embedding C D) (f : Embedding D A) : Embedding C A where
  point := f.point ∘ e.point
  sort_eq x := (f.sort_eq (e.point x)).trans (e.sort_eq x)
  map_func F x y hy := f.map_func F (e.point x) (e.point y) (e.map_func F x y hy)
  map_rel R xs hx := f.map_rel R (e.point ∘ xs) (e.map_rel R xs hx)
  injective x y h := e.injective (f.injective h)
  reflect_func F x y hy := by
    obtain ⟨z,hz,hzy⟩ := f.reflect_func F (e.point x) y hy
    obtain ⟨q,hq,hqz⟩ := e.reflect_func F x z hz
    exact ⟨q,hq,(congrArg f.point hqz).trans hzy⟩
  reflect_rel R xs hx := e.reflect_rel R xs (f.reflect_rel R (e.point ∘ xs) hx)

theorem embedding_homEmbedding {V : Type v} {W : Type w}
    {C : Structure L V} {D : Structure L W} (e : Embedding C D) :
    e.toHom.HomEmbedding := by
  intro A hA _hIr
  refine ⟨fun _ _ _ _ h => e.injective h, ?_, ?_⟩
  · intro R xs _hxs
    exact ⟨e.reflect_rel R xs,e.map_rel R xs⟩
  · intro F x hx y hy
    obtain ⟨z,hz,hzy⟩ := e.reflect_func F x y hy
    exact ⟨z,hA F x hx hz,hz,hzy⟩

/-- Postcomposition into a possibly different carrier universe. -/
def hom_postcompose_embedding {V : Type v} {W : Type w} {T : Type t}
    {C : Structure L V} {D : Structure L W} {A : Structure L T}
    (f : Hom C D) (e : Embedding D A) : Hom C A where
  point := e.point ∘ f.point
  sort_eq x := (e.sort_eq (f.point x)).trans (f.sort_eq x)
  map_func F x y hy := e.map_func F (f.point x) (f.point y) (f.map_func F x y hy)
  map_rel R xs hx := e.map_rel R (f.point ∘ xs) (f.map_rel R xs hx)

theorem homEmbedding_postcompose_embedding {V : Type v} {W : Type w} {T : Type t}
    {C : Structure L V} {D : Structure L W} {A : Structure L T}
    (f : Hom C D) (hf : f.HomEmbedding) (e : Embedding D A) :
    (hom_postcompose_embedding f e).HomEmbedding := by
  intro B hB hIr
  apply (embeddingOn_iff_closed_induced (hom_postcompose_embedding f e) B hB).mpr
  exact ⟨embedding_comp (f.restrictionEmbedding hB (hf B hB hIr)) e,fun _ => rfl⟩

/-- Every abstract irreducible source diagram is tested through its
actual induced closed image. The target embedding is exactly f after e. -/
theorem homEmbedding_to_rawHE {V W : Type v}
    {C : Structure L V} {D : Structure L W} (f : Hom C D)
    (hf : f.HomEmbedding) : CCO.UnaryHN.Raw.HE C D f.point := by
  refine ⟨f.sort_eq,f.map_func,f.map_rel,?_⟩
  intro X E hE e
  let A := Set.range e.point
  let hA : C.IsClosed A := embedding_range_closed e
  have hIr : (C.induce A hA).Irreducible := embedding_image_irreducible e hE
  let k := f.restrictionEmbedding hA (hf A hA hIr)
  exact ⟨embedding_comp (embedding_image_iso e).toEmbedding k,fun _ => rfl⟩

/-- Test the actual subset inclusion; the returned embedding has the
same map on every element of the closed irreducible source subset. -/
theorem rawHE_to_homEmbedding {V W : Type v}
    {C : Structure L V} {D : Structure L W} (f : Hom C D)
    (hf : CCO.UnaryHN.Raw.HE C D f.point) : f.HomEmbedding := by
  intro A hA hIr
  obtain ⟨e,he⟩ := hf.irreducibles (C.induce A hA) hIr (C.inclusion A hA)
  exact (embeddingOn_iff_closed_induced f A hA).mpr ⟨e,he⟩

theorem homEmbedding_iff_rawHE {V W : Type v}
    {C : Structure L V} {D : Structure L W} (f : Hom C D) :
    f.HomEmbedding ↔ CCO.UnaryHN.Raw.HE C D f.point :=
  ⟨homEmbedding_to_rawHE f,rawHE_to_homEmbedding f⟩

theorem rawHE_postcompose {V W T : Type v}
    {C : Structure L V} {D : Structure L W} {A : Structure L T}
    {f : V → W} (hf : CCO.UnaryHN.Raw.HE C D f) (e : Embedding D A) :
    CCO.UnaryHN.Raw.HE C A (e.point ∘ f) :=
  homEmbedding_to_rawHE (hom_postcompose_embedding hf.toHom e)
    (homEmbedding_postcompose_embedding hf.toHom (rawHE_to_homEmbedding hf.toHom hf) e)

end
end CCO.TerminalHiddenHN
