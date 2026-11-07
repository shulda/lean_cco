import CCO.UnfilteredEP.HierarchyComparisons
import CCO.UnfilteredEP.HierarchyNormalizedAge
import CCO.ResetOrder.Hierarchy.Reversal

/-!
# B064 C49: legal relative reversal of one independent actual task orbit

Reverse the whole selected transition orbit, reconstruct every finer
parent-lex comparison by the SAME coarse-first rule, and retain the old
carrier/functions/cylinders. Every other independent parent-fibre task is
unchanged. The resulting full expansion belongs to the SAME normalized age.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ResetOrder.Hierarchy CCO.FullCode
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (proper : ∀ x, ProperSort B ht (C.sort x)) (hC : ActualAge B ht C)
variable (priority : LinearOrder (Sig B ht).Sorts)

/-- Assemble ANY actual family of sort orders using the same fixed
hidden-sort priority and exactly the old carrier decomposition. -/
@[instance_reducible] def globalOrderOfCutOrders
    (orders : (reindexedCutSystem B ht C hC).Orders) : LinearOrder V :=
  linearOrderOfStrict ((sortOrder (orbitSortPriority B ht priority) orders).pullback
    (orbitCarrierEquiv B ht C proper) (orbitCarrierEquiv B ht C proper).injective)

theorem globalOrderOfCutOrders_same (orders : (reindexedCutSystem B ht C hC).Orders)
    (i : Sigma (CutInOrbit B ht))
    (x y : HiddenCutCarrier B ht C (cutOrbitEquiv B ht i)) :
    @LT.lt _ (globalOrderOfCutOrders B ht C proper hC priority orders).toLT x.val y.val ↔
      (orders i).lt x y := by
  change (sortOrder (orbitSortPriority B ht priority) orders).lt
    (orbitCarrierEquiv B ht C proper x.val) (orbitCarrierEquiv B ht C proper y.val) ↔ _
  have hx := (orbitCarrierEquiv B ht C proper).apply_symm_apply ⟨i,x⟩
  have hy := (orbitCarrierEquiv B ht C proper).apply_symm_apply ⟨i,y⟩
  rw [orbitCarrierEquiv_symm] at hx hy
  rw [hx,hy]
  exact sortOrder_same (orbitSortPriority B ht priority) orders i x y

theorem cutInputOrders_globalOrder (orders : (reindexedCutSystem B ht C hC).Orders) :
    cutInputOrders B ht C hC (globalOrderOfCutOrders B ht C proper hC priority orders) = orders := by
  funext i
  apply TotalOrder.ext
  intro x y
  exact globalOrderOfCutOrders_same B ht C proper hC priority orders i x y

variable (o : LinearOrder V) (selected : CutOrbit B ht)

def reversedCutOrders : (reindexedCutSystem B ht C hC).Orders :=
  (actualCutCharting B ht C hC).reverseOrbit (cutInputOrders B ht C hC o) selected

/-- Reversed local tasks remain synchronized because an ENTIRE orbit
is reversed; both endpoints of every path receive the same reversal. -/
theorem reversedCutOrders_synchronized :
    (actualCutCharting B ht C hC).Synchronized (reversedCutOrders B ht C hC o selected) := by
  intro r j k p x y hp
  let S := reindexedCutSystem B ht C hC
  let chart := actualCutCharting B ht C hC
  have hp' := (chart.parent_transport r p x y).mpr hp
  change (S.normalizeTasks (S.reverseTasks (chart.localTasks (cutInputOrders B ht C hC o))
    (fun i => i.1 = selected)) ⟨r,k⟩).lt _ _ ↔
      (S.normalizeTasks (S.reverseTasks (chart.localTasks (cutInputOrders B ht C hC o))
        (fun i => i.1 = selected)) ⟨r,j⟩).lt x y
  rw [S.normalized_fibre _ _ hp',S.normalized_fibre _ _ hp]
  classical
  by_cases hr : r = selected
  · rw [S.reverseTasks_selected _ (fun i => i.1 = selected) ⟨r,k⟩ hr,
      S.reverseTasks_selected _ (fun i => i.1 = selected) ⟨r,j⟩ hr]
    exact chart.localTasks_synchronized (cutInputOrders B ht C hC o) r p y x
  · simp only [System.reverseTasks,if_neg hr]
    exact chart.localTasks_synchronized (cutInputOrders B ht C hC o) r p x y

theorem reversedCutOrders_parentLex :
    (reindexedCutSystem B ht C hC).ParentLex (reversedCutOrders B ht C hC o selected) := by
  let S := reindexedCutSystem B ht C hC
  have hf : S.normalize (reversedCutOrders B ht C hC o selected) =
      reversedCutOrders B ht C hC o selected := by
    unfold System.normalize reversedCutOrders Charting.reverseOrbit
    rw [S.extract_normalize]
  rw [← hf]
  exact S.normalize_parentLex _

/-- The SAME actual normalizer fixes this reversed full order family. -/
theorem reversedCutOrders_fixed :
    (actualCutCharting B ht C hC).normalize (reversedCutOrders B ht C hC o selected) =
      reversedCutOrders B ht C hC o selected :=
  ((actualCutCharting B ht C hC).fixed_iff_image _).mpr
    ⟨reversedCutOrders_parentLex B ht C hC o selected,
      reversedCutOrders_synchronized B ht C hC o selected⟩

@[instance_reducible] def reverseHierarchicalOrder : LinearOrder V :=
  globalOrderOfCutOrders B ht C proper hC priority (reversedCutOrders B ht C hC o selected)

theorem reverseHierarchicalOrder_fixed :
    hierarchicalOrder B ht C proper hC priority
      (reverseHierarchicalOrder B ht C proper hC priority o selected) =
      reverseHierarchicalOrder B ht C proper hC priority o selected := by
  change globalOrderOfCutOrders B ht C proper hC priority
    ((actualCutCharting B ht C hC).normalize
      (cutInputOrders B ht C hC
        (globalOrderOfCutOrders B ht C proper hC priority (reversedCutOrders B ht C hC o selected)))) = _
  rw [cutInputOrders_globalOrder,reversedCutOrders_fixed]
  rfl

/-- Legal reversal lies in the SAME whole normalized proper hidden age. -/
theorem reverseHierarchicalOrder_mem [Finite V] :
    NormalizedProperAge B ht priority
      ⟨V,@OrderedCoordinateModel B ht V C
        (reverseHierarchicalOrder B ht C proper hC priority o selected),inferInstance⟩ :=
  ⟨C,reverseHierarchicalOrder B ht C proper hC priority o selected,hC,proper,
    reverseHierarchicalOrder_fixed B ht C proper hC priority o selected,rfl⟩

/-- The selected task flips in ALL its transported parent fibres. -/
theorem reverseHierarchicalOrder_selected (j : CutInOrbit B ht selected)
    (x y : HiddenCutCarrier B ht C j.val)
    (hp : (actualCutSystem B ht C hC).parent j.val x y) :
    @LT.lt _ (reverseHierarchicalOrder B ht C proper hC priority o selected).toLT x.val y.val ↔
      @LT.lt _ (hierarchicalOrder B ht C proper hC priority o).toLT y.val x.val := by
  let S := reindexedCutSystem B ht C hC
  let chart := actualCutCharting B ht C hC
  refine (globalOrderOfCutOrders_same B ht C proper hC priority
    (reversedCutOrders B ht C hC o selected) ⟨selected,j⟩ x y).trans ?_
  change (chart.reverseOrbit (cutInputOrders B ht C hC o) selected ⟨selected,j⟩).lt x y ↔ _
  rw [chart.reverseOrbit_local _ selected j x y hp]
  have hs := S.normalized_fibre (chart.localTasks (cutInputOrders B ht C hC o))
    ⟨selected,j⟩ ((S.parent_symm _) hp)
  exact hs.symm.trans (hierarchicalOrder_same B ht C proper hC priority o ⟨selected,j⟩ y x).symm

/-- Every OTHER independent task is unchanged, in particular every
previously exposed task in any coarse-first finite enumeration. -/
theorem reverseHierarchicalOrder_other_parent (r : CutOrbit B ht) (hr : r ≠ selected)
    (j : CutInOrbit B ht r) (x y : HiddenCutCarrier B ht C j.val)
    (hp : (actualCutSystem B ht C hC).parent j.val x y) :
    @LT.lt _ (reverseHierarchicalOrder B ht C proper hC priority o selected).toLT x.val y.val ↔
      @LT.lt _ (hierarchicalOrder B ht C proper hC priority o).toLT x.val y.val := by
  let S := reindexedCutSystem B ht C hC
  let chart := actualCutCharting B ht C hC
  refine (globalOrderOfCutOrders_same B ht C proper hC priority
    (reversedCutOrders B ht C hC o selected) ⟨r,j⟩ x y).trans ?_
  have hs := S.normalized_fibre
    (S.reverseTasks (chart.localTasks (cutInputOrders B ht C hC o)) (fun i => i.1 = selected)) ⟨r,j⟩ hp
  refine hs.trans ?_
  classical
  simp only [System.reverseTasks,if_neg hr]
  exact (S.normalized_fibre (chart.localTasks (cutInputOrders B ht C hC o)) ⟨r,j⟩ hp).symm.trans
    (hierarchicalOrder_same B ht C proper hC priority o ⟨r,j⟩ x y).symm

/-- Finer lexicographic comparisons are recomputed; all STRICTLY coarser
sort orders remain literally the old normalized sort orders. -/
theorem reverseHierarchicalOrder_coarser (i : Sigma (CutInOrbit B ht))
    (hi : (actualCutSchedule B).rank (cutOrbitEquiv B ht i) <
      (actualCutSchedule B).rank (cutRepresentative B ht selected).val) :
    reversedCutOrders B ht C hC o selected i = normalizedCutOrders B ht C hC o i :=
  (actualCutCharting B ht C hC).reverseOrbit_coarser (cutInputOrders B ht C hC o) selected i hi

end
end CCO.UnfilteredEP
