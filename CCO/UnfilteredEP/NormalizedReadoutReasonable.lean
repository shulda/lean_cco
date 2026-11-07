import CCO.UnfilteredEP.NormalizedReadoutSupport

/-! Reasonableness of the exact normalized full readout class. The old
visible map is prescribed first and remains literally the same map. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1000000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
local notation "Γ" => actualTupleInterpretation B ht F

/-- A hidden map on the canonical prescribed support points reflects
the whole readout order on those exact points. -/
def readoutEmbeddingOfSupportMap
    {A E : FiniteInduced (X := B.Point)}
    {a : (Γ).ReadoutOn A} {b : (Γ).ReadoutOn E}
    (f : InducedEmbedding B.source A E)
    (g : Structure.Embedding (actualOrderedTemplate B ht F a).model
      (actualOrderedTemplate B ht F b).model)
    (points : ∀ x, g.point x = ((Γ).supportEmbedding B.homogeneous f).point x) :
    (Γ).ReadoutEmbedding B.homogeneous a b where
  old := f
  order_iff x y := by
    have hh := g.binary_iff (.inr (((Γ).supportStructure A).sort x,
      ((Γ).supportStructure A).sort y)) x y
    change ((((Γ).supportStructure E).sort (g.point x) =
        ((Γ).supportStructure A).sort x) ∧
      (((Γ).supportStructure E).sort (g.point y) =
        ((Γ).supportStructure A).sort y) ∧ @LT.lt _ b.order.toLT (g.point x) (g.point y)) ↔
      (((Γ).supportStructure A).sort x = ((Γ).supportStructure A).sort x ∧
        ((Γ).supportStructure A).sort y = ((Γ).supportStructure A).sort y ∧
        @LT.lt _ a.order.toLT x y) at hh
    have hx : ((Γ).supportStructure E).sort (g.point x) =
        ((Γ).supportStructure A).sort x := g.sort_eq x
    have hy : ((Γ).supportStructure E).sort (g.point y) =
        ((Γ).supportStructure A).sort y := g.sort_eq y
    rw [hx,hy] at hh
    simpa only [true_and,points] using hh

/-- Concrete hidden reasonableness extends ANY normalized source
readout along the supplied original map, without replacing that map. -/
theorem normalized_readout_reasonable
    (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct)
    (oldAge : ∀ D, ages.oldAge D ↔ ProperFiniteCodeAge B ht D)
    (proper : ∀ D, ages.expandedAge D → ProperOrderedAge B ht D)
    {A E : FiniteInduced (X := B.Point)} (f : InducedEmbedding B.source A E)
    (a : (Γ).ReadoutOn A) (member : ages.expandedAge (actualOrderedTemplate B ht F a)) :
    ∃ b : (Γ).ReadoutOn E, ages.expandedAge (actualOrderedTemplate B ht F b) ∧
      (Γ).restrictReadout B.homogeneous f b = a := by
  let aHidden : ExpansionOn (coordinateOrderExpansion B ht).toReduct
      ages.expandedAge (actualOldSupport B ht F A) := ⟨_,rfl,member⟩
  obtain ⟨e,g,points⟩ := ages.reasonable (actualOldSupport B ht F A)
    (actualOldSupport B ht F E)
    ((oldAge _).mpr (actualOldSupport_mem B ht F A))
    ((oldAge _).mpr (actualOldSupport_mem B ht F E))
    (actualOldSupportMap B ht F f) aHidden
  obtain ⟨b,equal⟩ := expansionOn_actualOldSupport B ht F ages.expandedAge proper E e
  have memberB : ages.expandedAge (actualOrderedTemplate B ht F b) := by
    have hh := e.member
    change ages.expandedAge ⟨_,(actualOrderedTemplate B ht F b).model,_⟩
    rw [← equal]
    exact hh
  let h := readoutEmbeddingOfSupportMap B ht F f (g.targetCongr equal) points
  refine ⟨b,memberB,?_⟩
  apply TupleInterpretation.ReadoutOn.ext
  apply LinearOrder.ext_lt
  exact h.order_iff

end
end CCO.UnfilteredEP
