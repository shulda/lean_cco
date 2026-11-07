import CCO.UnfilteredEP.NormalizedReadoutData
import CCO.UnfilteredEP.HostTemplateEmbedding

/-! Ramsey transfer for the exact normalized full code. The arbitrary
hidden witness retains all its roots and all its generated support. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1000000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
open CCO.TerminalHiddenHN
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct)
variable (oldAge : ∀ D, ages.oldAge D ↔ ProperFiniteCodeAge B ht D)
variable (proper : ∀ D, ages.expandedAge D → ProperOrderedAge B ht D)
local notation "Γ" => actualTupleInterpretation B ht F
local notation "Eₙ" => normalizedReadoutData B ht F ages oldAge proper

/-- Hidden Ramsey arrows of the SAME normalized class transfer to its
full original finite relational readout. No order EP is used here. -/
theorem normalized_readout_data_ramsey
    (ramsey : HasHiddenRamsey ages.expandedAge) : (Eₙ).Ramsey := by
  intro A E a b n positive
  obtain ⟨D,member,arrow⟩ := ramsey (actualOrderedTemplate B ht F a.val)
    (actualOrderedTemplate B ht F b.val) a.property b.property n positive
  obtain ⟨C,o,hC,equal⟩ := (proper D member).1
  rcases D with ⟨W,M,finiteW⟩
  dsimp only at C o hC equal member arrow
  subst M
  let : Finite W := finiteW
  let : LinearOrder W := o
  let R := actualHostReadout B ht F C hC
  have normalized : ages.expandedAge (actualOrderedTemplate B ht F R.readout) :=
    hidden_member_of_embedding ages.expandedAge ages.expandedHereditary
      ages.expandedIsoClosed member (hostReadoutTemplateMap B ht F R)
  let c : (Eₙ).Expansion R.old := ⟨R.readout,normalized⟩
  refine ⟨R.old,c,?_⟩
  intro colour
  obtain ⟨g,shade,mono⟩ := actualReadout_arrow B ht F a.val b.val R arrow
    (fun f => colour (readoutToNormalized B ht F ages oldAge proper (a := a) (b := c) f))
  refine ⟨readoutToNormalized B ht F ages oldAge proper (a := b) (b := c) g,?_⟩
  have constant (f : (Eₙ).Embedding a b) :
      colour ((readoutToNormalized B ht F ages oldAge proper (a := b) (b := c) g).comp f) = shade := by
    have equal : (readoutToNormalized B ht F ages oldAge proper (a := b) (b := c) g).comp f =
        readoutToNormalized B ht F ages oldAge proper (a := a) (b := c)
          (g.comp B.homogeneous (normalizedToReadout B ht F ages oldAge proper f)) :=
      RealExpansionData.Embedding.ext (fun _ => rfl)
    exact (congrArg colour equal).trans
      (mono (normalizedToReadout B ht F ages oldAge proper f))
  exact fun f h => (constant f).trans (constant h).symm

end
end CCO.UnfilteredEP
