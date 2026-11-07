import CCO.UnfilteredEP.OrderedMidpointExtension
import CCO.UnfilteredEP.HierarchyMaps
import CCO.UnfilteredEP.HierarchyComparisons

/-! Actual free order extension for ONE independent representative task.
The whole prescribed normalized base order is retained on the SAME map.
The midpoint is inserted only in its actual parent fibre, then all finer
lexicographic comparisons are reconstructed by the actual normalizer. -/

universe u v w z a
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

/-- C62/C64: no comparison on the whole old base is discarded. The two
parent-key hypotheses refer to the actual ALL-coarser-key system and will
be supplied by the actual reset witness on the same finite hidden member. -/
theorem normalized_midpoint_order_extension
    (priority : LinearOrder (Sig B ht).Sorts)
    {V : Type z} {W : Type a}
    {C : Structure (Sig B ht) V} {D : Structure (Sig B ht) W}
    (hC : ActualAge B ht C) (hD : ActualAge B ht D)
    (properC : ∀ x, ProperSort B ht (C.sort x))
    (properD : ∀ x, ProperSort B ht (D.sort x))
    (e : C.Embedding D) (oC : LinearOrder V)
    (fixed : hierarchicalOrder B ht C properC hC priority oC = oC)
    (r : CutOrbit B ht)
    (left right : HiddenCutCarrier B ht C (cutRepresentative B ht r).val)
    (midpoint : HiddenCutCarrier B ht D (cutRepresentative B ht r).val)
    (fresh : midpoint.val ∉ Set.range e.point)
    (beforeParent : (actualCutSystem B ht D hD).parent (cutRepresentative B ht r).val
      ((cutGeometryMap B ht hC hD e).point _ left) midpoint)
    (afterParent : (actualCutSystem B ht D hD).parent (cutRepresentative B ht r).val
      midpoint ((cutGeometryMap B ht hC hD e).point _ right))
    (comparison : @LT.lt _ oC.toLT left.val right.val) :
    ∃ oD : LinearOrder W,
      hierarchicalOrder B ht D properD hD priority oD = oD ∧
      (∀ x y, @LT.lt _ oD.toLT (e.point x) (e.point y) ↔ @LT.lt _ oC.toLT x y) ∧
      @LT.lt _ oD.toLT (e.point left.val) midpoint.val ∧
      @LT.lt _ oD.toLT midpoint.val (e.point right.val) := by
  letI : Finite W := hD.1
  obtain ⟨raw,keeps,before,after⟩ := OrderedAmalgamInsertion.finite_insert_over_whole_base
    oC ⟨e.point,e.injective⟩ midpoint.val fresh left.val right.val comparison
  let normalized := hierarchicalOrder B ht D properD hD priority raw
  refine ⟨normalized,hierarchicalOrder_idempotent B ht D properD hD priority raw,?_,?_,?_⟩
  · intro x y
    have law := hierarchicalOrder_map_iff B ht hC hD e oC raw keeps properC properD priority x y
    rw [fixed] at law
    exact law
  · exact (hierarchicalOrder_representative_parent B ht D properD hD priority raw r
      ((cutGeometryMap B ht hC hD e).point _ left) midpoint beforeParent).mpr before
  · exact (hierarchicalOrder_representative_parent B ht D properD hD priority raw r
      midpoint ((cutGeometryMap B ht hC hD e).point _ right) afterParent).mpr after

end
end CCO.UnfilteredEP
