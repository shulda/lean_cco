import CCO.UnfilteredEP.OrderedTaskFibreOrders
import CCO.UnfilteredEP.TaskPrefixLanguage

/-! Extension of one next task preserves the ENTIRE earlier prefix
strictly on the same target carrier, including every earlier task
comparison and all old partial graphs and semantic fine relations. -/

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
universe u v w z a
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

theorem normalized_prefix_order_extension
    (priority : LinearOrder (Sig B ht).Sorts)
    {V : Type z} {W : Type a} {C : Structure (Sig B ht) V} {D : Structure (Sig B ht) W}
    (hC : ActualAge B ht C) (hD : ActualAge B ht D)
    (properD : ∀ x, ProperSort B ht (D.sort x))
    (e : C.Embedding D) (oC : LinearOrder V) (oD : LinearOrder W)
    (i : Fin (taskCount B ht)) (n : Nat) (earlier : n ≤ i.val) :
    ∃ o : LinearOrder W,
      hierarchicalOrder B ht D properD hD priority o = o ∧
      taskPrefixData B ht n (@OrderedCoordinateModel B ht W D o) =
        taskPrefixData B ht n (@OrderedCoordinateModel B ht W D oD) ∧
      (∀ x y : HiddenCutCarrier B ht C (taskCut B ht i),
        (actualCutSystem B ht C hC).parent (taskCut B ht i) x y →
        (@LT.lt _ o.toLT (e.point x.val) (e.point y.val) ↔ @LT.lt _ oC.toLT x.val y.val)) := by
  obtain ⟨o,fixed,selected,other⟩ := normalized_task_order_extension B ht priority
    hC hD properD e oC oD (taskEnumeration B ht i)
  refine ⟨o,fixed,?_,selected⟩
  apply CCO.FullCode.Structure.ext_data
    (C := taskPrefixData B ht n (@OrderedCoordinateModel B ht W D o))
    (D := taskPrefixData B ht n (@OrderedCoordinateModel B ht W D oD)) rfl rfl rfl
  funext R x y
  cases R with
  | inl R => rfl
  | inr j =>
    apply propext
    change ((actualParentFormula B ht (taskCut B ht j.val)).same (CoordinateModel B ht D) x y ∧
      (D.sort x = hiddenCutSort B ht (taskCut B ht j.val) ∧
       D.sort y = hiddenCutSort B ht (taskCut B ht j.val) ∧ @LT.lt _ o.toLT x y)) ↔
      ((actualParentFormula B ht (taskCut B ht j.val)).same (CoordinateModel B ht D) x y ∧
      (D.sort x = hiddenCutSort B ht (taskCut B ht j.val) ∧
       D.sort y = hiddenCutSort B ht (taskCut B ht j.val) ∧ @LT.lt _ oD.toLT x y))
    by_cases hp : (actualParentFormula B ht (taskCut B ht j.val)).same (CoordinateModel B ht D) x y
    · let xx : HiddenCutCarrier B ht D (taskCut B ht j.val) := ⟨x,hp.1⟩
      let yy : HiddenCutCarrier B ht D (taskCut B ht j.val) := ⟨y,hp.2.1⟩
      have parent := (actualParentFormula_same_iff B ht D hD (taskCut B ht j.val) xx yy).mp hp
      have different : taskEnumeration B ht j.val ≠ taskEnumeration B ht i := by
        intro h
        have equal := (taskEnumeration B ht).injective h
        have hj := Nat.lt_of_lt_of_le j.property earlier
        exact (Nat.ne_of_lt hj) (congrArg Fin.val equal)
      have comparison := other (taskEnumeration B ht j.val) different xx yy parent
      exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl comparison))
    · simp only [hp,false_and]

end
end CCO.UnfilteredEP
