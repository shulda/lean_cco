import CCO.UnfilteredEP.OwnerTemplate

/-! Exact original point maps between the independent finite-age
presentation and the actual source's induced finite embeddings. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.CloneTupleGeometry CCO.APCharacter
noncomputable section

private def colourCode (B : OwnerStage.{u,v,w}) (c : Age.Colour B.source) :
    Option (OwnerOriginalAtom B) := c.2.2.map (fun a => ⟨c.1,c.2.1,a⟩)

private theorem tagged_of_sort_and_code (B : OwnerStage.{u,v,w})
    {p q r s : Sigma B.Point} (hp : p.1 = r.1) (hq : q.1 = s.1)
    (hc : colourCode B (taggedColour B.source p q) =
      colourCode B (taggedColour B.source r s)) :
    taggedColour B.source p q = taggedColour B.source r s := by
  rcases p with ⟨i,p⟩
  rcases q with ⟨j,q⟩
  rcases r with ⟨k,r⟩
  rcases s with ⟨l,s⟩
  dsimp only at hp hq
  subst k
  subst l
  have hinj : Function.Injective (fun a : B.source.Atom i j =>
      (⟨i,j,a⟩ : OwnerOriginalAtom B)) := by
    intro a b h
    simpa only [Sigma.mk.injEq,heq_eq_eq,true_and] using h
  have ho : B.source.colour p q = B.source.colour r s := Option.map_injective hinj hc
  exact congrArg (fun c => (⟨i,j,c⟩ : Age.Colour B.source)) ho

/-- All fine atoms, logical equality and the original sort predicates
are preserved on exactly the original supplied point map. -/
def ownerEmbeddingToInduced (B : OwnerStage.{u,v,w})
    {A E : FiniteInduced (X := B.Point)} (f : (ownerFiniteAge B).Embedding A E) :
    InducedEmbedding B.source A E where
  toEmbedding := ⟨f.toFun,f.injective⟩
  preserves_sort := f.sorted
  preserves_colours x y := (tagged_of_sort_and_code B (f.sorted x) (f.sorted y) (f.colours x y)).symm

/-- The inverse presentation retains the same point map. -/
def ownerEmbeddingOfInduced (B : OwnerStage.{u,v,w})
    {A E : FiniteInduced (X := B.Point)} (f : InducedEmbedding B.source A E) :
    (ownerFiniteAge B).Embedding A E where
  toFun := f.toEmbedding
  injective := f.toEmbedding.injective
  sorted := f.preserves_sort
  colours x y := congrArg (colourCode B) (f.preserves_colours x y).symm

@[simp] theorem ownerEmbeddingToInduced_toEmbedding (B : OwnerStage.{u,v,w})
    {A E : FiniteInduced (X := B.Point)} (f : (ownerFiniteAge B).Embedding A E)
    (x : A.vertices) : (ownerEmbeddingToInduced B f).toEmbedding x = f.toFun x := rfl

@[simp] theorem ownerEmbeddingOfInduced_toFun (B : OwnerStage.{u,v,w})
    {A E : FiniteInduced (X := B.Point)} (f : InducedEmbedding B.source A E)
    (x : A.vertices) : (ownerEmbeddingOfInduced B f).toFun x = f.toEmbedding x := rfl

end
end CCO.UnfilteredEP
