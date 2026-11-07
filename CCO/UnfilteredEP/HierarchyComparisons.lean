import CCO.UnfilteredEP.HierarchyOrders

/-! Concrete receiving comparison laws for the SAME actual normalized
hidden class: fixed sort priority, synchronized same-parent paths, and
retention of a chosen representative task's original fibre order. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.ResetOrder.Hierarchy
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable {V : Type z} (C : CCO.UnarySupport.Structure (Sig B ht) V)
variable (proper : ∀ x, ProperSort B ht (C.sort x)) (hC : ActualAge B ht C)
variable (priority : LinearOrder (Sig B ht).Sorts) (o : LinearOrder V)

/-- The symbol at the carrier decomposition is exactly its original
actual hidden SORT, not a new chart-dependent name. -/
theorem orbitCarrierEquiv_sort (x : V) :
    hiddenCutSort B ht (cutOrbitEquiv B ht (orbitCarrierEquiv B ht C proper x).1) = C.sort x := by
  have hx : (orbitCarrierEquiv B ht C proper x).2.val = x :=
    (orbitCarrierEquiv B ht C proper).symm_apply_apply x
  exact (orbitCarrierEquiv B ht C proper x).2.property.symm.trans (congrArg C.sort hx)

/-- Cross-sort comparisons are the fixed hidden sort-symbol priority. -/
theorem hierarchicalOrder_different_sort (x y : V) (hne : C.sort x ≠ C.sort y) :
    @LT.lt _ (hierarchicalOrder B ht C proper hC priority o).toLT x y ↔
      @LT.lt _ priority.toLT (C.sort x) (C.sort y) := by
  change (@LT.lt _ priority.toLT
    (hiddenCutSort B ht (cutOrbitEquiv B ht (orbitCarrierEquiv B ht C proper x).1))
    (hiddenCutSort B ht (cutOrbitEquiv B ht (orbitCarrierEquiv B ht C proper y).1)) ∨
      ∃ h : (orbitCarrierEquiv B ht C proper x).1 = (orbitCarrierEquiv B ht C proper y).1,
        (normalizedCutOrders B ht C hC o (orbitCarrierEquiv B ht C proper y).1).lt
          (h ▸ (orbitCarrierEquiv B ht C proper x).2)
          (orbitCarrierEquiv B ht C proper y).2) ↔ _
  rw [orbitCarrierEquiv_sort B ht C proper,orbitCarrierEquiv_sort B ht C proper]
  constructor
  · rintro (h | ⟨he,_⟩)
    · exact h
    · exact False.elim (hne ((orbitCarrierEquiv_sort B ht C proper x).symm.trans
        ((congrArg (fun i => hiddenCutSort B ht (cutOrbitEquiv B ht i)) he).trans
          (orbitCarrierEquiv_sort B ht C proper y))))
  · exact Or.inl

/-- A named quotient path preserves normalized order WITHIN its true
parent fibres. Global monotonicity across different fibres is not claimed. -/
theorem hierarchicalOrder_path_parent {D E : HiddenCut B}
    (p : NamedCutPath B ht D E) (x y : HiddenCutCarrier B ht C D)
    (hp : (actualCutSystem B ht C hC).parent D x y) :
    @LT.lt _ (hierarchicalOrder B ht C proper hC priority o).toLT
      (finitePathEquiv B ht C hC p x).val (finitePathEquiv B ht C hC p y).val ↔
      @LT.lt _ (hierarchicalOrder B ht C proper hC priority o).toLT x.val y.val := by
  let paths := NamedCutPath.ambientPaths (B := B) (ht := ht)
  let r := paths.orbit D
  let j : CutInOrbit B ht r := ⟨D,rfl⟩
  let k : CutInOrbit B ht r := ⟨E,Quotient.sound ⟨p.inverse⟩⟩
  have hs := (actualCutCharting B ht C hC).normalize_synchronized
    (cutInputOrders B ht C hC o) r (j := j) (k := k) p x y hp
  exact (hierarchicalOrder_same B ht C proper hC priority o ⟨r,k⟩ _ _).trans
    (hs.trans (hierarchicalOrder_same B ht C proper hC priority o ⟨r,j⟩ x y).symm)

/-- In a representative cut, normalization retains the independently
chosen within-parent comparison literally. This supplies midpoint insertion
without prescribing incompatible finer parent-lex comparisons. -/
theorem hierarchicalOrder_representative_parent (r : CutOrbit B ht)
    (x y : HiddenCutCarrier B ht C (cutRepresentative B ht r).val)
    (hp : (actualCutSystem B ht C hC).parent (cutRepresentative B ht r).val x y) :
    @LT.lt _ (hierarchicalOrder B ht C proper hC priority o).toLT x.val y.val ↔
      @LT.lt _ o.toLT x.val y.val := by
  let chart := actualCutCharting B ht C hC
  let i := (⟨r,cutRepresentative B ht r⟩ : Sigma (CutInOrbit B ht))
  have hs := (reindexedCutSystem B ht C hC).normalized_fibre
    (chart.localTasks (cutInputOrders B ht C hC o)) i hp
  refine (hierarchicalOrder_same B ht C proper hC priority o i x y).trans (hs.trans ?_)
  change (_ ∧ @LT.lt _ o.toLT (chart.back r (cutRepresentative B ht r) x).val
    (chart.back r (cutRepresentative B ht r) y).val) ↔ _
  rw [chart.back_representative,chart.back_representative]
  exact and_iff_right hp

end
end CCO.UnfilteredEP
