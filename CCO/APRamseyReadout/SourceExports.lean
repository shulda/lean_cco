import CCO.APRamseyReadout.GeneralExpansion
import CCO.APRamseyReadout.CoordinateCompletion
import CCO.APRamseyReadout.OrderedRigidity
import CCO.APRamseyReadout.FiniteSourceExpansion
import CCO.APRamseyReadout.OrderCodeBoundary
import CCO.APRamseyReadout.VisibleJEP
import CCO.APRamseyReadout.VisibleRigidity

/-! B061's five source result anchors, preserving their full original
quantifiers. The general AP theorem constructs a new safe terminal clone
endpoint. The parameterized readout APIs remain public for ANY genuine
terminal owner stage and ANY fixed distinct meet-K chart. Marked template
maps target ALL host roots; completion stays in the SAME actual host.
The independent block theorem retains only its A04 assumptions.

The smaller source theorem has no hidden Ramsey/readout callback: its
actual proper block Ramsey instance is discharged in RamseyReadout.
The finite-source diagnostic is separate from the infinite AP theorem;
no expansion property or EPPA assertion is included. -/

namespace CCO.APRamseyReadout.Source

universe u v w p
open CCO.CloneTupleGeometry
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)

/-- Ordinary AP for the SAME actual expanded age. No strong-intersection
conclusion is inferred from the visible Ramsey arrow. -/
theorem actual_full_readout_ap : ExpandedAP (actualFullReadoutData B ht F) :=
  expandedAP_of_ramsey_jep _ (actual_full_readout_ramsey B ht F)
    (actual_full_readout_jep B ht F)

theorem actual_small_readout_ap (priority : LinearOrder (CoordinateLanguage B ht).Sorts) :
    ExpandedAP (actualSmallReadoutData B ht F priority) :=
  expandedAP_of_ramsey_jep _ (actual_small_readout_ramsey B ht F priority)
    (actual_small_readout_jep B ht F priority)

export CCO.APRamseyReadout
  (general_ap_ramsey_expansion general_ap_full_ramsey_expansion
   general_ap_small_ramsey_expansion
   actual_template_embeddings actual_template_presentations actual_template_extension_unique
   actual_coordinate_completion actualCompletionMap actualCompletionMap_selected actual_completion_empty
   sort_block_normalization
   terminal_full_readout_expansion terminal_small_readout_expansion
   actualFullReadoutData actualSmallReadoutData
   actualFullReadoutData_reasonable actualSmallReadoutData_reasonable
   actual_full_readout_ramsey actual_block_readout_ramsey actual_small_readout_ramsey
   actual_full_readout_jep actual_small_readout_jep
   actual_full_readout_rigid actual_small_readout_rigid
   actual_ordered_visible_rigid)

end CCO.APRamseyReadout.Source
