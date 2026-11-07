import CCO.UnfilteredEP.OwnerTemplateProviderSingletons
import CCO.UnfilteredEP.OwnerTemplatePairs
import CCO.UnfilteredEP.OwnerTemplateCore
import CCO.UnfilteredEP.FiniteCoreCriterion

/-! Actual unfiltered unary EP. The same given genuine history supplies
its exact pair-local age and automatic core. The SAME full block-code
provider supplies singleton arrows; order EP is not used here. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
open CCO.APRamseyReadout
noncomputable section
variable {B D : OwnerStage.{u,v,w}}

/-- C88–C89: every actual terminal label is retained. The fixed original
host precedes EVERY competing legal full marking of that host. -/
theorem owner_unfiltered_unary_EP
    (base : B.Sorts) (one : ∀ i : B.Sorts, base = i)
    (history : History OwnerStage.Next B D) (terminal : D.Terminal)
    (F : Charts.{u,v,w,p} D)
    (priority : LinearOrder (CoordinateLanguage D terminal).Sorts) :
    (ownerFiniteAge B).UnaryEP (ownerTemplate history) := by
  let _ := D.source.finiteSort
  let _ := B.source.finiteSort
  let _ := B.source.finiteAtom
  exact (ownerTemplateProvider history terminal F priority).unary_EP_of_finite_template_core
    (owner_template_provider_singletons history terminal F priority)
    (owner_template_provider_reductSurjective history terminal F priority)
    (owner_template_provider_jep history terminal F priority)
    (owner_template_provider_ramsey history terminal F priority)
    (owner_template_pairs_realized history)
    (actual_owner_template_core base one history terminal)

end
end CCO.UnfilteredEP
