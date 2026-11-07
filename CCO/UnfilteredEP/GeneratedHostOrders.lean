import CCO.UnfilteredEP.HiddenAgeTransport
import CCO.APRamseyReadout.ActualReadout

/-!
# Every competing full readout gives orders on the same hidden host

The old support equivalence is fixed first. The entire competing support
order is then pulled onto that exact carrier, with all equalities,
function graphs and fine cylinders unchanged. No replacement competitor
and no preferred expanded host is selected.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p z
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable {W : Type (max u v)} {C : CCO.UnarySupport.Structure (Sig B ht) W} [LinearOrder W]
variable (R : HostReadout B ht F C)
variable (generated : RootGenerated (CoordinateModel B ht C) (tupleScheme B ht F))
local notation "Γ" => actualTupleInterpretation B ht F

/-- Pull back the ENTIRE supplied competitor order along the fixed
old support inverse. The carrier W was already chosen. -/
@[instance_reducible] def generatedHostOrder (b : (Γ).ReadoutOn R.old) : LinearOrder W := by
  let e := generatedHostSupportEquiv B ht F R generated
  letI := b.order
  exact LinearOrder.lift' e.symm e.symm.injective

/-- The same canonical support map preserves every competitor comparison. -/
theorem generatedHostOrder_comparison (b : (Γ).ReadoutOn R.old)
    (x y : (Γ).support R.old) :
    @LT.lt W (generatedHostOrder B ht F R generated b).toLT
      (R.support.point x) (R.support.point y) ↔ @LT.lt _ b.order.toLT x y := by
  let e := generatedHostSupportEquiv B ht F R generated
  change @LT.lt _ b.order.toLT (e.symm (e x)) (e.symm (e y)) ↔ _
  rw [e.symm_apply_apply,e.symm_apply_apply]

/-- Same old source, same embedding, same old host roots and support map.
Only the arbitrary competitor's order has been transported. -/
def reorderedHostReadout (b : (Γ).ReadoutOn R.old) :
    @HostReadout B ht F W C (generatedHostOrder B ht F R generated b) :=
  @HostReadout.mk B ht F W C (generatedHostOrder B ht F R generated b)
    R.embedding R.old R.vertices_eq R.roots R.roots_owner R.support R.support_root b
    (fun x y => (generatedHostOrder_comparison B ht F R generated b x y).symm)

/-- All unary domains, complete non-order codes and order comparisons
are transported by the SAME canonical support point map. -/
def generatedOrderedSupportMap (b : (Γ).ReadoutOn R.old) :
    Structure.Embedding (actualOrderedTemplate B ht F b).model
      (@OrderedCoordinateModel B ht W C (generatedHostOrder B ht F R generated b)) where
  point := R.support.point
  injective := R.support.injective
  sort_eq := R.support.sort_eq
  map_func := R.support.map_func
  reflect_func := R.support.reflect_func
  unary_iff U := PEmpty.elim U
  binary_iff predicate x y := by
    cases predicate with
    | inl predicate =>
      have hh := R.support.binary_iff predicate x y
      have hb := congrArg (fun M : Structure (CoordinateLanguage B ht) ((Γ).support R.old) =>
        M.binary predicate x y) (actualTemplateRaw_binary B ht F R.old).symm
      exact hh.trans (Iff.of_eq hb)
    | inr sorts =>
      change ((CoordinateModel B ht C).sort (R.support.point x) = sorts.1 ∧
        (CoordinateModel B ht C).sort (R.support.point y) = sorts.2 ∧
        @LT.lt W (generatedHostOrder B ht F R generated b).toLT
          (R.support.point x) (R.support.point y)) ↔
        (((Γ).supportStructure R.old).sort x = sorts.1 ∧
          ((Γ).supportStructure R.old).sort y = sorts.2 ∧ @LT.lt _ b.order.toLT x y)
      rw [R.support.sort_eq,R.support.sort_eq]
      exact and_congr Iff.rfl (and_congr Iff.rfl
        (generatedHostOrder_comparison B ht F R generated b x y))

/-- Transport preserves membership in ANY actual iso-closed full order
class. In particular this applies to the synchronized normalized class. -/
theorem generated_ordered_host_member
    (K : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht) → Prop)
    (isoClosed : HiddenIsoClosed K) [Finite W]
    (b : (Γ).ReadoutOn R.old) (member : K (actualOrderedTemplate B ht F b)) :
    K ⟨W,@OrderedCoordinateModel B ht W C (generatedHostOrder B ht F R generated b),inferInstance⟩ :=
  hidden_member_of_bijective_embedding K isoClosed member
    (generatedOrderedSupportMap B ht F R generated b)
    (generated_host_support_surjective B ht F R generated)

end
end CCO.UnfilteredEP
