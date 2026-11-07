import CCO.UnfilteredEP.HierarchyNormalizedAge

/-! Actual fixed-source maps into a normalized host. All casts retain the
same vertex maps; this is the concrete bridge used by the ONE-class Ramsey
and joint-embedding arguments. -/

set_option backward.isDefEq.respectTransparency.types false
universe u v w z a
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.FullCode
noncomputable section

namespace FullEmbedding
variable {L : Language.{u}} {V : Type v} {W : Type w}
variable {C C' : Structure L V} {D D' : Structure L W}

def castModels (e : Structure.Embedding C D) (hC : C = C') (hD : D = D') :
    Structure.Embedding C' D' := hC ▸ hD ▸ e

@[simp] theorem castModels_point (e : Structure.Embedding C D) (hC : C = C') (hD : D = D')
    (x : V) : (castModels e hC hD).point x = e.point x := by
  cases hC
  cases hD
  rfl
end FullEmbedding

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)

structure NormalizedPresentation (A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)) where
  raw : CCO.UnarySupport.Structure (Sig B ht) A.Carrier
  order : LinearOrder A.Carrier
  actual : ActualAge B ht raw
  proper : ∀ x, ProperSort B ht (raw.sort x)
  fixed : hierarchicalOrder B ht raw proper actual priority order = order
  model_eq : A.model = @OrderedCoordinateModel B ht A.Carrier raw order

def normalizedPresentation {A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)}
    (hA : NormalizedProperAge B ht priority A) : NormalizedPresentation B ht priority A :=
  Classical.choice (by
    obtain ⟨C,o,hC,proper,hfixed,heq⟩ := hA
    exact ⟨⟨C,o,hC,proper,hfixed,heq⟩⟩)

variable {A : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)}
variable (hA : NormalizedProperAge B ht priority A)
variable {W : Type a} (C : CCO.UnarySupport.Structure (Sig B ht) W)
variable (proper : ∀ x, ProperSort B ht (C.sort x)) (hC : ActualAge B ht C)

/-- Fixed sources embed into the normalized host along EXACTLY the old
supplied embedding, with every domain/value/relation retained. -/
def fixedIntoNormalizedHost (o : LinearOrder W)
    (e : Structure.Embedding A.model (@OrderedCoordinateModel B ht W C o)) :
    Structure.Embedding A.model (normalizedCoordinateModel B ht priority C proper hC o) := by
  let P := normalizedPresentation B ht priority hA
  let e0 := FullEmbedding.castModels e P.model_eq rfl
  let e1 := normalizedOrderedEmbedding B ht priority P.raw P.proper P.actual proper hC P.order o e0
  let e2 := FullEmbedding.castModels e1
    (congrArg (fun o => @OrderedCoordinateModel B ht A.Carrier P.raw o) P.fixed) rfl
  exact FullEmbedding.castModels e2 P.model_eq.symm rfl

@[simp] theorem fixedIntoNormalizedHost_point (o : LinearOrder W)
    (e : Structure.Embedding A.model (@OrderedCoordinateModel B ht W C o)) (x : A.Carrier) :
    (fixedIntoNormalizedHost B ht priority hA C proper hC o e).point x = e.point x := by
  simp only [fixedIntoNormalizedHost,FullEmbedding.castModels_point,normalizedOrderedEmbedding_point]

end
end CCO.UnfilteredEP
