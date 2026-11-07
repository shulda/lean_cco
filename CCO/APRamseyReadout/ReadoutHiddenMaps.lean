import CCO.APRamseyReadout.ActualReadout

/-! A selected original readout map induces the actual ordered hidden
template map on the SAME canonical support points. Every partial domain,
non-order cylinder and global comparison is preserved and reflected.
No inverse from arbitrary hidden maps to selected roots is asserted. -/

universe u v w p
namespace CCO.APRamseyReadout
open CCO.CloneTupleGeometry CCO.FullCode
noncomputable section

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)

/-- The full ordered hidden map uses literally the original map's
canonical full induced support embedding, with its entire unary domains. -/
def actualTemplateEmbedding
    {A E : CCO.FiniteInduced (X := B.Point)}
    {a : (actualFullReadoutData B ht F).Expansion A}
    {b : (actualFullReadoutData B ht F).Expansion E}
    (f : (actualTupleInterpretation B ht F).ReadoutEmbedding B.homogeneous a b) :
    Structure.Embedding (actualOrderedTemplate B ht F a).model
      (actualOrderedTemplate B ht F b).model where
  point := ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point
  injective := ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).injective
  sort_eq := ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).sort_eq
  map_func := ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).map_func
  reflect_func := ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).reflect_func
  unary_iff U := PEmpty.elim U
  binary_iff R x y := by
    cases R with
    | inl R =>
      change (CoordinateModel B ht (actualTemplateRaw B ht F E)).binary R
          (((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point x)
          (((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point y) ↔
        (CoordinateModel B ht (actualTemplateRaw B ht F A)).binary R x y
      rw [actualTemplateRaw_binary B ht F E,actualTemplateRaw_binary B ht F A]
      exact ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).binary_iff R x y
    | inr sorts =>
      change (((actualTupleInterpretation B ht F).supportStructure E).sort (((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point x) =
            sorts.1 ∧
          ((actualTupleInterpretation B ht F).supportStructure E).sort (((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point y) =
            sorts.2 ∧
          @LT.lt _ b.order.toLT (((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point x)
            (((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point y)) ↔
        (((actualTupleInterpretation B ht F).supportStructure A).sort x = sorts.1 ∧
          ((actualTupleInterpretation B ht F).supportStructure A).sort y = sorts.2 ∧ @LT.lt _ a.order.toLT x y)
      rw [((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).sort_eq x,
        ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).sort_eq y,f.order_iff x y]

@[simp] theorem actualTemplateEmbedding_point
    {A E : CCO.FiniteInduced (X := B.Point)}
    {a : (actualFullReadoutData B ht F).Expansion A}
    {b : (actualFullReadoutData B ht F).Expansion E}
    (f : (actualTupleInterpretation B ht F).ReadoutEmbedding B.homogeneous a b) (x : actualTupleSupport B ht F A) :
    (actualTemplateEmbedding B ht F f).point x =
      ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point x := rfl

/-- Every coordinate of the image is the coordinate of the prescribed
selected old target root, not a newly selected compatible tuple. -/
theorem actualTemplateEmbedding_root
    {A E : CCO.FiniteInduced (X := B.Point)}
    {a : (actualFullReadoutData B ht F).Expansion A}
    {b : (actualFullReadoutData B ht F).Expansion E}
    (f : (actualTupleInterpretation B ht F).ReadoutEmbedding B.homogeneous a b) (x : A.vertices) :
    (actualOrderedRoot B ht F a x).map (actualTemplateEmbedding B ht F f) =
      actualOrderedRoot B ht F b (f.old.toEmbedding x) := by
  apply Root.ext_coordinates
    (r := (actualOrderedRoot B ht F a x).map (actualTemplateEmbedding B ht F f))
    (s := actualOrderedRoot B ht F b (f.old.toEmbedding x))
    (((actualTupleInterpretation B ht F).codeEmbedding B.homogeneous f.old).tag_eq x).symm
  intro j
  exact (actualTupleInterpretation B ht F).supportEmbedding_coordinate B.homogeneous f.old x j

@[simp] theorem actualTemplateEmbedding_id
    {A : CCO.FiniteInduced (X := B.Point)} (a : (actualFullReadoutData B ht F).Expansion A) :
    actualTemplateEmbedding B ht F (TupleInterpretation.ReadoutEmbedding.id B.homogeneous a) =
      Structure.Embedding.id (actualOrderedTemplate B ht F a).model := by
  apply Structure.Embedding.ext
  intro x
  change ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous (TupleInterpretation.oldId A)).point x = x
  rw [(actualTupleInterpretation B ht F).supportEmbedding_id]
  rfl

theorem actualTemplateEmbedding_comp
    {A E K : CCO.FiniteInduced (X := B.Point)}
    {a : (actualFullReadoutData B ht F).Expansion A}
    {b : (actualFullReadoutData B ht F).Expansion E}
    {c : (actualFullReadoutData B ht F).Expansion K}
    (g : (actualTupleInterpretation B ht F).ReadoutEmbedding B.homogeneous b c) (f : (actualTupleInterpretation B ht F).ReadoutEmbedding B.homogeneous a b) :
    actualTemplateEmbedding B ht F (g.comp B.homogeneous f) =
      (actualTemplateEmbedding B ht F g).comp (actualTemplateEmbedding B ht F f) := by
  apply Structure.Embedding.ext
  intro x
  change ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous (TupleInterpretation.oldComp g.old f.old)).point x =
    ((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous g.old).point (((actualTupleInterpretation B ht F).supportEmbedding B.homogeneous f.old).point x)
  rw [(actualTupleInterpretation B ht F).supportEmbedding_comp]
  rfl

end
end CCO.APRamseyReadout
