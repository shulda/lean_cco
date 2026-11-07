import CCO.UnfilteredEP.NormalizedExpansionFields
import CCO.UnfilteredEP.HierarchyRamsey

/-! The actual expansion-age package used by every relative order task
and by the full-code transfer. All fields are concretely discharged. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.FullCode
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)

/-- ONE actual proper hidden age and its synchronized normalized
expansion on the same finite carriers, including all orphan vertices. -/
def actualNormalizedExpansionAges :
    ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct where
  oldAge := ProperFiniteCodeAge B ht
  expandedAge := NormalizedProperAge B ht priority
  oldHereditary := proper_finite_code_hereditary B ht
  expandedHereditary := normalized_proper_hereditary B ht priority
  expandedIsoClosed := normalized_proper_isoClosed B ht priority
  reductMember := normalized_reduct_member B ht priority
  reductSurjective := normalized_reduct_surjective B ht priority
  reasonable := normalized_expansion_reasonable B ht priority
  precompact D _ := finite_expansionOn _ _ D

theorem actual_normalized_old_age (D) :
    (actualNormalizedExpansionAges B ht priority).oldAge D ↔ ProperFiniteCodeAge B ht D := Iff.rfl

theorem actual_normalized_expanded_proper (D)
    (member : (actualNormalizedExpansionAges B ht priority).expandedAge D) :
    ProperOrderedAge B ht D := normalizedProperAge_to_proper B ht priority member

theorem actual_normalized_hidden_ramsey :
    HasHiddenRamsey (actualNormalizedExpansionAges B ht priority).expandedAge :=
  normalized_proper_ramsey B ht priority

end
end CCO.UnfilteredEP
