import CCO.UnfilteredEP.HierarchyMaps
import CCO.UnfilteredEP.HierarchyComparisons
import CCO.UnfilteredEP.OrderedAmalgamFiniteOrder
import Mathlib.Logic.Function.Basic

/-! Finite extension of ONE independent representative-sort order.
Every other actual cut-sort order is retained before normalization.
Consequently every other representative parent-fibre task is retained
after the actual normalization, independently of any task enumeration. -/

set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
universe u v w z a
namespace CCO.UnfilteredEP
open APRamseyReadout CloneTupleGeometry UnarySupport ResetOrder.Hierarchy
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

def taskExtensionGlobalOrder {V : Type z} (C : Structure (Sig B ht) V)
    (proper : ∀ x, ProperSort B ht (C.sort x))
    (priority : LinearOrder (Sig B ht).Sorts)
    (orders : ∀ D : HiddenCut B, TotalOrder (HiddenCutCarrier B ht C D)) : LinearOrder V :=
  linearOrderOfStrict ((sortOrder
    ((strictOrderOfLinear priority).pullback (hiddenCutSort B ht) (hiddenCutSort_injective B ht))
    orders).pullback (cutCarrierEquiv B ht C proper) (cutCarrierEquiv B ht C proper).injective)

theorem taskExtensionGlobalOrder_same {V : Type z} (C : Structure (Sig B ht) V)
    (proper : ∀ x, ProperSort B ht (C.sort x))
    (priority : LinearOrder (Sig B ht).Sorts)
    (orders : ∀ D : HiddenCut B, TotalOrder (HiddenCutCarrier B ht C D))
    (D : HiddenCut B) (x y : HiddenCutCarrier B ht C D) :
    @LT.lt _ (taskExtensionGlobalOrder B ht C proper priority orders).toLT x.val y.val ↔
      (orders D).lt x y := by
  change (sortOrder _ orders).lt (cutCarrierEquiv B ht C proper x.val)
    (cutCarrierEquiv B ht C proper y.val) ↔ _
  have hx : cutCarrierEquiv B ht C proper x.val = ⟨D,x⟩ :=
    (cutCarrierEquiv B ht C proper).apply_symm_apply ⟨D,x⟩
  have hy : cutCarrierEquiv B ht C proper y.val = ⟨D,y⟩ :=
    (cutCarrierEquiv B ht C proper).apply_symm_apply ⟨D,y⟩
  rw [hx,hy]
  exact sortOrder_same _ orders D x y

/-- The prescribed source representative-sort order extends along its
SAME typed point map. All other target cut-sort comparisons stay fixed. -/
theorem one_cut_order_extension
    (priority : LinearOrder (Sig B ht).Sorts)
    {V : Type z} {W : Type a} {C : Structure (Sig B ht) V} {D : Structure (Sig B ht) W}
    (hC : ActualAge B ht C) (hD : ActualAge B ht D)
    (properD : ∀ x, ProperSort B ht (D.sort x))
    (e : C.Embedding D) (oC : LinearOrder V) (oD : LinearOrder W) (selected : HiddenCut B) :
    ∃ o : LinearOrder W,
      (∀ x y : HiddenCutCarrier B ht C selected,
        (@LT.lt _ o.toLT (e.point x.val) (e.point y.val) ↔ @LT.lt _ oC.toLT x.val y.val)) ∧
      (∀ E : HiddenCut B, E ≠ selected → ∀ x y : HiddenCutCarrier B ht D E,
        (@LT.lt _ o.toLT x.val y.val ↔ @LT.lt _ oD.toLT x.val y.val)) := by
  classical
  letI : Finite W := hD.1
  let f := (cutGeometryMap B ht hC hD e).point selected
  let source : TotalOrder (HiddenCutCarrier B ht C selected) :=
    (strictOrderOfLinear oC).pullback Subtype.val Subtype.val_injective
  obtain ⟨chosen,extendsOrder⟩ := OrderedAmalgamInsertion.extend_finite source f
    ((cutGeometryMap B ht hC hD e).injective selected)
  let old : ∀ E : HiddenCut B, TotalOrder (HiddenCutCarrier B ht D E) :=
    fun _ => (strictOrderOfLinear oD).pullback Subtype.val Subtype.val_injective
  let orders := Function.update old selected chosen
  let result := taskExtensionGlobalOrder B ht D properD priority orders
  refine ⟨result,?_,?_⟩
  · intro x y
    have law := taskExtensionGlobalOrder_same B ht D properD priority orders selected (f x) (f y)
    rw [show orders selected = chosen from Function.update_self _ _ _] at law
    exact law.trans (extendsOrder x y)
  · intro E different x y
    have law := taskExtensionGlobalOrder_same B ht D properD priority orders E x y
    rw [show orders E = old E from Function.update_of_ne different _ _] at law
    exact law

theorem cutRepresentative_injective : Function.Injective
    (fun r : CutOrbit B ht => (cutRepresentative B ht r).val) := by
  intro r s h
  exact (cutRepresentative B ht r).property.symm.trans
    ((congrArg (NamedCutPath.ambientPaths (B := B) (ht := ht)).orbit h).trans
      (cutRepresentative B ht s).property)

/-- The actual normalized extension retains EVERY other independent
parent-fibre task and extends the selected one on the SAME induced map. -/
theorem normalized_task_order_extension
    (priority : LinearOrder (Sig B ht).Sorts)
    {V : Type z} {W : Type a} {C : Structure (Sig B ht) V} {D : Structure (Sig B ht) W}
    (hC : ActualAge B ht C) (hD : ActualAge B ht D)
    (properD : ∀ x, ProperSort B ht (D.sort x))
    (e : C.Embedding D) (oC : LinearOrder V) (oD : LinearOrder W) (r : CutOrbit B ht) :
    ∃ o : LinearOrder W,
      hierarchicalOrder B ht D properD hD priority o = o ∧
      (∀ x y : HiddenCutCarrier B ht C (cutRepresentative B ht r).val,
        (actualCutSystem B ht C hC).parent (cutRepresentative B ht r).val x y →
        (@LT.lt _ o.toLT (e.point x.val) (e.point y.val) ↔ @LT.lt _ oC.toLT x.val y.val)) ∧
      (∀ s : CutOrbit B ht, s ≠ r →
        ∀ x y : HiddenCutCarrier B ht D (cutRepresentative B ht s).val,
        (actualCutSystem B ht D hD).parent (cutRepresentative B ht s).val x y →
        (@LT.lt _ o.toLT x.val y.val ↔ @LT.lt _ oD.toLT x.val y.val)) := by
  obtain ⟨raw,selected,other⟩ := one_cut_order_extension B ht priority hC hD properD e oC oD
    (cutRepresentative B ht r).val
  refine ⟨hierarchicalOrder B ht D properD hD priority raw,
    hierarchicalOrder_idempotent B ht D properD hD priority raw,?_,?_⟩
  · intro x y parent
    have hp := ((cutGeometryMap B ht hC hD e).parent_iff _ x y).mpr parent
    exact (hierarchicalOrder_representative_parent B ht D properD hD priority raw r
      ((cutGeometryMap B ht hC hD e).point _ x)
      ((cutGeometryMap B ht hC hD e).point _ y) hp).trans (selected x y)
  · intro s different x y parent
    exact (hierarchicalOrder_representative_parent B ht D properD hD priority raw s x y parent).trans
      (other _ (fun h => different (cutRepresentative_injective B ht h)) x y)

end
end CCO.UnfilteredEP
