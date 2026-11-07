import CCO.UnfilteredEP.OwnerTemplateProvider

/-! Ramsey/JEP and reduct-surjectivity of the SAME actual FULL-code
provider. No EP or automatic core theorem is used in these constructions. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.CloneTupleGeometry CCO.APCharacter CCO.APCharacter.Towers
open CCO.APRamseyReadout CCO.TerminalHiddenHN
noncomputable section

variable {B D : OwnerStage.{u,v,w}} (history : History OwnerStage.Next B D)
variable (terminal : D.Terminal) (F : Charts.{u,v,w,p} D)
variable (priority : LinearOrder (CoordinateLanguage D terminal).Sorts)
local notation "P" => OwnerStage.historyReduct history
local notation "E" => actualFullBlockReadoutData D terminal F priority
local notation "R" => ownerTemplateProvider history terminal F priority

/-- The original pair-local unary age is reduct-surjective by a real
endpoint inverse image of every old point. -/
theorem owner_template_reductSurjective :
    (ownerFiniteAge B).ReductSurjective (ownerTemplate history) := by
  intro A
  exact ⟨reductMarkingOfLift P (UnaryLift.canonicalLift P A)⟩

/-- ALL pair-legal joint markings, not only previously chosen markings,
have genuine full block expansions by the actual whole-history theorem. -/
theorem owner_template_provider_reductSurjective : (R).ReductSurjective := by
  intro A a
  obtain ⟨L,hL⟩ := owner_marking_lift history A a
  let c := Classical.choice ((E).nonempty L.object)
  let X : OwnerProviderObject history terminal F priority := ⟨A,L,c⟩
  exact ⟨X,⟨FiniteAge.Embedding.id A,hL⟩,Function.surjective_id⟩

/-- The actual terminal full-block joint host is read back over the
original source through its literal complete unary reduct. -/
theorem owner_template_provider_jep : (R).JEP := by
  intro A B
  obtain ⟨C,c,⟨left⟩,⟨right⟩⟩ := actual_full_block_readout_jep D terminal F priority
    A.2.1.object B.2.1.object A.2.2 B.2.2
  let old := UnaryLift.projectedObject P C
  let N := UnaryLift.canonicalLift P old
  let d := (E).restrict (UnaryLift.projectedEmbedding P C) c
  let inverse := UnaryLift.projectedExpandedInverse P E C c
  let out : OwnerProviderObject history terminal F priority := ⟨old,N,d⟩
  refine ⟨out,?_,?_⟩
  · exact ⟨ownerProviderEmbeddingOfReal history terminal F priority
      (UnaryLift.toOldEmbedding P E A.2.1 N (inverse.comp left))⟩
  · exact ⟨ownerProviderEmbeddingOfReal history terminal F priority
      (UnaryLift.toOldEmbedding P E B.2.1 N (inverse.comp right))⟩

/-- Existing full-block Ramsey arrows survive the literal old reduct.
Every generic provider embedding corresponds to a genuine full-code map,
so the colourings range over ALL permitted embeddings. -/
theorem owner_template_provider_ramsey : (R).Ramsey := by
  intro A B n positive
  obtain ⟨C,c,hC⟩ := UnaryLift.ramsey P E
    (actual_full_block_readout_ramsey D terminal F priority)
    A.1 B.1 (ownerProviderExpansion history terminal F priority A)
    (ownerProviderExpansion history terminal F priority B) n positive
  rcases c with ⟨table,L,d,rfl⟩
  let out : OwnerProviderObject history terminal F priority := ⟨C,L,d⟩
  refine ⟨out,?_⟩
  intro colour
  obtain ⟨g,hg⟩ := hC (fun f => colour (ownerProviderEmbeddingOfReal history terminal F priority f))
  refine ⟨ownerProviderEmbeddingOfReal history terminal F priority g,?_⟩
  intro f h
  have mono := hg (ownerProviderEmbeddingToReal history terminal F priority f)
    (ownerProviderEmbeddingToReal history terminal F priority h)
  simpa only [ownerProviderEmbeddingOfReal_comp] using mono

end
end CCO.UnfilteredEP
