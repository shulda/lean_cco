import CCO.UnfilteredEP.HierarchyMaps

/-!
# B064 C69--C70 receiving map: all independent tasks recover the full order

An old induced embedding need preserve only the representative within-parent
fibre tasks. Existing named charts transport these comparisons to every
copy, and the coarse-first recursion then recovers every full normalized
comparison. No premise preserving the derived parent-lex order is assumed.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z a
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ResetOrder.Hierarchy
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable {V : Type z} {W : Type a}
variable {C : CCO.UnarySupport.Structure (Sig B ht) V}
variable {D : CCO.UnarySupport.Structure (Sig B ht) W}
variable (hC : ActualAge B ht C) (hD : ActualAge B ht D) (e : C.Embedding D)
variable (oC : LinearOrder V) (oD : LinearOrder W)

def PreservesRepresentativeTasks : Prop :=
  ∀ (r : CutOrbit B ht)
    (x y : HiddenCutCarrier B ht C (cutRepresentative B ht r).val),
    (actualCutSystem B ht C hC).parent (cutRepresentative B ht r).val x y →
    @LT.lt _ oC.toLT x.val y.val → @LT.lt _ oD.toLT (e.point x.val) (e.point y.val)

include oC oD in
/-- Chart synchronization requires only the actual representative task,
not a globally monotone transition or an extra coarser-order premise. -/
theorem localTasks_preserve_of_representative
    (tasks : PreservesRepresentativeTasks B ht hC e oC oD)
    (i : Sigma (CutInOrbit B ht))
    (x y : HiddenCutCarrier B ht C (cutOrbitEquiv B ht i))
    (h : ((actualCutCharting B ht C hC).localTasks (cutInputOrders B ht C hC oC) i).lt x y) :
    ((actualCutCharting B ht D hD).localTasks (cutInputOrders B ht D hD oD) i).lt
      ((orbitGeometryMap B ht hC hD e).point i x) ((orbitGeometryMap B ht hC hD e).point i y) := by
  rcases i with ⟨r,j⟩
  refine ⟨((orbitGeometryMap B ht hC hD e).parent_iff _ x y).mpr h.1,?_⟩
  have hp := ((actualCutCharting B ht C hC).parent_back r j x y).mpr h.1
  have hh := tasks r ((actualCutCharting B ht C hC).back r j x)
    ((actualCutCharting B ht C hC).back r j y) hp h.2
  change @LT.lt _ oD.toLT
    ((actualCutCharting B ht D hD).back r j ((orbitGeometryMap B ht hC hD e).point ⟨r,j⟩ x)).val
    ((actualCutCharting B ht D hD).back r j ((orbitGeometryMap B ht hC hD e).point ⟨r,j⟩ y)).val
  rw [actual_chart_back_commutes B ht hC hD e,actual_chart_back_commutes B ht hC hD e]
  exact hh

variable (properC : ∀ x, ProperSort B ht (C.sort x))
variable (properD : ∀ x, ProperSort B ht (D.sort x))

/-- Reconstruction of ALL normalized global comparisons from precisely
the independent representative tasks. -/
theorem hierarchicalOrder_map_of_representative_tasks
    (tasks : PreservesRepresentativeTasks B ht hC e oC oD)
    (priority : LinearOrder (Sig B ht).Sorts) (x y : V) :
    @LT.lt _ (hierarchicalOrder B ht D properD hD priority oD).toLT (e.point x) (e.point y) ↔
      @LT.lt _ (hierarchicalOrder B ht C properC hC priority oC).toLT x y := by
  let f := orbitGeometryMap B ht hC hD e
  have fibre (i : Sigma (CutInOrbit B ht))
      (x y : HiddenCutCarrier B ht C (cutOrbitEquiv B ht i)) :
      (normalizedCutOrders B ht D hD oD i).lt (f.point i x) (f.point i y) ↔
        (normalizedCutOrders B ht C hC oC i).lt x y :=
    f.normalize_reflects _ _ (localTasks_preserve_of_representative B ht hC hD e oC oD tasks) i x y
  have preserve : ∀ x y,
      @LT.lt _ (hierarchicalOrder B ht C properC hC priority oC).toLT x y →
      @LT.lt _ (hierarchicalOrder B ht D properD hD priority oD).toLT (e.point x) (e.point y) := by
    intro x y hxy
    change (sortOrder (orbitSortPriority B ht priority) (normalizedCutOrders B ht D hD oD)).lt
      (orbitCarrierEquiv B ht D properD (e.point x)) (orbitCarrierEquiv B ht D properD (e.point y))
    rw [orbitCarrierEquiv_natural B ht hC hD e properC properD,
      orbitCarrierEquiv_natural B ht hC hD e properC properD]
    exact sortOrder_map (orbitSortPriority B ht priority) _ _ f.point
      (fun i x y h => (fibre i x y).mpr h) _ _ hxy
  constructor
  · intro h
    by_cases he : x = y
    · subst y
      exact False.elim (@lt_irrefl _ (hierarchicalOrder B ht D properD hD priority oD).toPreorder _ h)
    · letI := hierarchicalOrder B ht C properC hC priority oC
      rcases lt_or_gt_of_ne he with hxy | hyx
      · exact hxy
      · exact False.elim (@lt_asymm _ (hierarchicalOrder B ht D properD hD priority oD).toPreorder
          _ _ h (preserve y x hyx))
  · exact preserve x y

/-- The actual final-prefix receiving theorem: when the two sources are
fixed, all independent tasks already force the original full normalized
order on the SAME induced point map. -/
theorem hierarchy_fixed_map_of_representative_tasks
    (priority : LinearOrder (Sig B ht).Sorts)
    (fixedC : hierarchicalOrder B ht C properC hC priority oC = oC)
    (fixedD : hierarchicalOrder B ht D properD hD priority oD = oD)
    (tasks : PreservesRepresentativeTasks B ht hC e oC oD) (x y : V) :
    @LT.lt _ oD.toLT (e.point x) (e.point y) ↔ @LT.lt _ oC.toLT x y := by
  have h := hierarchicalOrder_map_of_representative_tasks B ht hC hD e oC oD properC properD tasks priority x y
  rw [fixedC,fixedD] at h
  exact h

end
end CCO.UnfilteredEP
