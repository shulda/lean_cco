import CCO.UnfilteredEP.ActualNormalizedReadout

/-! Joint embedding in the SAME normalized visible full-code age.
The whole hidden common host is read back, including every valid root. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1000000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct)
variable (oldAge : ∀ D, ages.oldAge D ↔ ProperFiniteCodeAge B ht D)
variable (proper : ∀ D, ages.expandedAge D → ProperOrderedAge B ht D)
local notation "Eₙ" => normalizedReadoutData B ht F ages oldAge proper

theorem normalized_readout_data_jep
    (jep : FullJointEmbedding (OrderedCoordinateLanguage B ht) ages.expandedAge) :
    ExpandedJEP (Eₙ) := by
  intro A E a b
  obtain ⟨D,member,⟨left⟩,⟨right⟩⟩ := jep (actualOrderedTemplate B ht F a.val)
    (actualOrderedTemplate B ht F b.val) a.property b.property
  obtain ⟨C,o,hC,equal⟩ := (proper D member).1
  rcases D with ⟨W,M,finiteW⟩
  dsimp only at C o hC equal member left right
  subst M
  let : Finite W := finiteW
  let : LinearOrder W := o
  let R := actualHostReadout B ht F C hC
  have normalized : ages.expandedAge (actualOrderedTemplate B ht F R.readout) :=
    hidden_member_of_embedding ages.expandedAge ages.expandedHereditary
      ages.expandedIsoClosed member (hostReadoutTemplateMap B ht F R)
  let c : (Eₙ).Expansion R.old := ⟨R.readout,normalized⟩
  exact ⟨R.old,c,
    ⟨readoutToNormalized B ht F ages oldAge proper (a := a) (b := c)
      (actualHiddenToReadout B ht F a.val R left)⟩,
    ⟨readoutToNormalized B ht F ages oldAge proper (a := b) (b := c)
      (actualHiddenToReadout B ht F b.val R right)⟩⟩

theorem actual_normalized_readout_jep
    (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    ExpandedJEP (actualNormalizedReadoutData B ht F priority) :=
  normalized_readout_data_jep B ht F _ _ _ (normalized_proper_jep B ht priority)

end
end CCO.UnfilteredEP
