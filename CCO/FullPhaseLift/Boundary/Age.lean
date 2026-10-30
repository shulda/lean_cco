import CCO.FullPhaseLift.Boundary.Class
import CCO.OwnerTransversal.CountableAge

/-! The boundary is an ACTUAL countable homogeneous full class. Its
Fraïssé realization is constructed from the preceding free amalgams,
independently of any support-normal hypothesis or model provider. -/

namespace CCO.FullPhaseLift.Boundary.HypergraphClass
open Canonical
open scoped FirstOrder
noncomputable section

structure Chart where
  size : ℕ
  full : BoolTable signature (Fin size)
  valid : Valid full

instance : Countable Chart := by
  apply Function.Injective.countable
    (f := fun C : Chart => (⟨C.size,C.full⟩ : Σ n, BoolTable signature (Fin n)))
  rintro ⟨n,T,ht⟩ ⟨m,V,hv⟩ h
  cases h
  rfl

abbrev emptyChart : Chart := ⟨0,table (fun (_ _ _ : Fin 0) => False),empty_valid _⟩
instance : Nonempty Chart := ⟨emptyChart⟩

def reindexIso {V : Type} (T : BoolTable signature V) {n : ℕ} (e : V ≃ Fin n) :
    Iso T (pullback T e.symm) :=
  isoOf e (by intro r xs; simp [pullback,Function.comp_def])

def finiteChart {V : Type} [Finite V] (T : BoolTable signature V) (hT : Valid T) : Chart := by
  classical
  letI := Fintype.ofFinite V
  let e := Fintype.equivFin V
  let T' := pullback T e.symm
  have hT' : Valid T' :=
    Valid.of_embedding (embeddingOf e.symm e.symm.injective (fun _ _ => rfl)) hT
  exact ⟨Fintype.card V,T',hT'⟩

def finiteChartIso {V : Type} [Finite V] (T : BoolTable signature V) (hT : Valid T) :
    Iso T (finiteChart T hT).full := by
  classical
  letI := Fintype.ofFinite V
  exact reindexIso T (Fintype.equivFin V)

def emptyEmbedding (C : Chart) : Embedding emptyChart.full C.full :=
  embeddingOf Fin.elim0 (fun x => Fin.elim0 x)
    (fun _ xs => Fin.elim0 (xs (0 : Fin 3)))

def foComp {A B C : Type} {TA : BoolTable signature A} {TB : BoolTable signature B}
    {TC : BoolTable signature C} (g : FirstOrderEmbedding TB TC) (f : FirstOrderEmbedding TA TB) :
    FirstOrderEmbedding TA TC := by
  letI := toFirstOrder TA
  letI := toFirstOrder TB
  letI := toFirstOrder TC
  exact g.comp f

theorem amalgamate (A B C : Chart)
    (f : FirstOrderEmbedding A.full B.full) (g : FirstOrderEmbedding A.full C.full) :
    ∃ (D : Chart) (l : FirstOrderEmbedding B.full D.full) (r : FirstOrderEmbedding C.full D.full),
      foComp l f = foComp r g := by
  let s := embeddingOfFirstOrder f
  let t := embeddingOfFirstOrder g
  obtain ⟨V,hV,T,hT,l,r,heq,_⟩ := strong_amalgamate A.full B.full C.full B.valid C.valid s t
  letI := hV
  let D := finiteChart T hT
  let e := (finiteChartIso T hT).toEmbedding
  refine ⟨D,embeddingToFirstOrder (e.comp l),embeddingToFirstOrder (e.comp r),?_⟩
  apply DFunLike.ext
  intro a
  exact congrArg e.point (heq a)

theorem hereditary (A : Type) [st : signature.firstOrder.Structure A] [Finite A]
    (C : Chart)
    (f : @FirstOrder.Language.Embedding signature.firstOrder A (Fin C.size)
      st (toFirstOrder C.full)) :
    ∃ D : Chart, Nonempty (@FirstOrder.Language.Equiv signature.firstOrder A (Fin D.size)
      st (toFirstOrder D.full)) := by
  let T := ofFirstOrder st
  have f' : FirstOrderEmbedding T C.full := by
    change @FirstOrder.Language.Embedding signature.firstOrder A (Fin C.size)
      (toFirstOrder (ofFirstOrder st)) (toFirstOrder C.full)
    rw [toFirstOrder_ofFirstOrder]
    exact f
  have hT : Valid T := Valid.of_embedding (embeddingOfFirstOrder f') C.valid
  let D := finiteChart T hT
  have e : FirstOrderIso T D.full := isoToFirstOrder (finiteChartIso T hT)
  refine ⟨D,⟨?_⟩⟩
  change @FirstOrder.Language.Equiv signature.firstOrder A (Fin D.size)
    (toFirstOrder (ofFirstOrder st)) (toFirstOrder D.full) at e
  rw [toFirstOrder_ofFirstOrder] at e
  exact e

def data : OwnerTransversal.CountableAge.Data signature.firstOrder where
  Chart := Chart
  Carrier C := Fin C.size
  finiteCarrier _ := inferInstance
  structureCarrier C := toFirstOrder C.full
  hereditary := hereditary
  joint B C := by
    obtain ⟨D,l,r,_⟩ := amalgamate emptyChart B C
      (embeddingToFirstOrder (emptyEmbedding B)) (embeddingToFirstOrder (emptyEmbedding C))
    exact ⟨D,⟨l⟩,⟨r⟩⟩
  amalgamate := amalgamate

abbrev Model := data.Limit
instance : Countable Model := inferInstance

def modelTable : BoolTable signature Model := ofFirstOrder (inferInstance : signature.firstOrder.Structure Model)

theorem model_homogeneous : signature.firstOrder.IsUltrahomogeneous Model := data.homogeneous

theorem model_infinite : Infinite Model := by
  apply data.infinite_of_unbounded
  intro n
  exact ⟨⟨n,table (fun (_ _ _ : Fin n) => False),empty_valid _⟩,
    ⟨Function.Embedding.refl (Fin n)⟩⟩

/-- Every actual valid finite full hypergraph embeds in the constructed
model, including each complete three-point factor and every empty-higher
finite set. -/
theorem valid_embeds {V : Type} [Finite V] (T : BoolTable signature V) (hT : Valid T) :
    Nonempty (Embedding T modelTable) := by
  let C := finiteChart T hT
  obtain ⟨p⟩ := data.chart_embeds C
  have p' : FirstOrderEmbedding C.full modelTable := by
    change @FirstOrder.Language.Embedding signature.firstOrder (Fin C.size) Model
      (toFirstOrder C.full) (toFirstOrder (ofFirstOrder inferInstance))
    rw [toFirstOrder_ofFirstOrder]
    exact p
  exact ⟨(embeddingOfFirstOrder p').comp (finiteChartIso T hT).toEmbedding⟩

/-- Conversely the FULL induced finite age contains only genuine class
objects; this will rule out the four-point completion, not merely one
particular attempted completion map. -/
theorem embedding_valid {V : Type} [Finite V] (T : BoolTable signature V)
    (f : Embedding T modelTable) : Valid T := by
  have f' : Nonempty (@FirstOrder.Language.Embedding signature.firstOrder V Model
      (toFirstOrder T) inferInstance) := by
    have g := embeddingToFirstOrder f
    change @FirstOrder.Language.Embedding signature.firstOrder V Model
      (toFirstOrder T) (toFirstOrder (ofFirstOrder inferInstance)) at g
    rw [toFirstOrder_ofFirstOrder] at g
    exact ⟨g⟩
  letI := toFirstOrder T
  obtain ⟨C,⟨e⟩⟩ := (data.finite_age V).mp f'
  exact Valid.of_embedding (embeddingOfFirstOrder e.toEmbedding) C.valid

theorem model_k4Free : K4Free (relation modelTable) := by
  intro f hf hc
  let T := pullback modelTable f
  let e : Embedding T modelTable := embeddingOf f hf (fun _ _ => rfl)
  have hT := embedding_valid T e
  apply hT.2.2 id Function.injective_id
  intro i j k hij hik hjk
  change modelTable 0 (f ∘ tuple3 i j k) = true
  rw [tuple3_comp]
  exact hc i j k hij hik hjk

end
end CCO.FullPhaseLift.Boundary.HypergraphClass
