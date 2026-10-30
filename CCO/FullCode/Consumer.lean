import CCO.FullCode.CodeLanguage
import CCO.FullCode.PresentationQuotient
import CCO.FullCode.Cofinality

/-! Actual use of FCODE with literal induced embeddings of the finite
visible signature, preserving the chosen source root marks. -/
universe u v w a
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type w}
  {C : Structure L V} {D : Structure L W} {S : RootScheme L} {A : Type a}

theorem Structure.Embedding.domain_iff (f : Structure.Embedding C D)
    (F : L.Func) (x : V) :
    (D.func F (f.point x)).Nonempty ↔ (C.func F x).Nonempty := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := f.reflect_func F x y hy
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨f.point z, f.map_func F x z hz⟩

/-- FCODE for the actual induced-map types of the explicit finite visible
language, rather than merely a chosen family of maps. -/
noncomputable def foundational_full_code_embeddings (N : NormalForms L)
    (O : Object C S A) (hC : N.Valid C) (hD : N.Valid D) :
    Structure.Embedding (O.codeStructure N) ((Object.full D S).codeStructure N) ≃
      Structure.Embedding O.supportStructure D :=
  (O.codeEmbeddingEquiv N (Object.full D S)).symm.trans (O.fullCodeEquiv N hC hD)

/-- One actual visible map yields one actual hidden extension. Its complete
partial domains are reflected, the literal root map is recovered, and no
second hidden extension can realize that same root map. -/
theorem full_code_embedding_use (N : NormalForms L) (O : Object C S A)
    (hC : N.Valid C) (hD : N.Valid D)
    (f : Structure.Embedding (O.codeStructure N) ((Object.full D S).codeStructure N)) :
    ∃ g : Structure.Embedding O.supportStructure D,
      (Object.fromHidden N O g).asCodeEmbedding = f ∧
      (∀ F x, (D.func F (g.point x)).Nonempty ↔ (O.supportStructure.func F x).Nonempty) ∧
      (∀ h : Structure.Embedding O.supportStructure D,
        (Object.fromHidden N O h).asCodeEmbedding = f → h = g) := by
  let e := foundational_full_code_embeddings N O hC hD
  refine ⟨e f, ?_, fun F x => (e f).domain_iff F x, ?_⟩
  · exact e.symm_apply_apply f
  · intro h hh
    apply e.symm.injective
    exact hh.trans (e.symm_apply_apply f).symm

/-- The reconstruction remembers the actual source coordinate classes;
the source root subset is never recovered from an unmarked support. -/
theorem marked_quotient_use (N : NormalForms L) (O : Object C S A) (hC : N.Valid C)
    (a : A) (j : Fin (S.arity (O.root a).tag)) :
    O.presentationQuotientEquiv N hC (O.coordinateClass N hC a j) =
      ⟨(O.root a).coordinate j, O.coordinate_mem_support a j⟩ := O.quotient_coordinate N hC a j

end CCO.FullCode
