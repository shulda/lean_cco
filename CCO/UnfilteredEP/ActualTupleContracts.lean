import CCO.UnfilteredEP.RootCoverage
import CCO.UnfilteredEP.TupleTransfer
import CCO.APRamseyReadout.ActualTupleSupport
import CCO.APRamseyReadout.FineReadout

/-!
# Actual cofinal and every-competitor same-host tuple contracts

The original terminal unary labels and fine atoms fix the unexpanded
coordinate-generated support. The chosen finite old host is constructed
before an arbitrary full-code competitor; its complete expansion is
transported onto that SAME existing host by the full-code equivalence.

This module is uniform in the hereditary normalized hidden order class.
Its actual concrete class and hidden EP are supplied separately by the
synchronized-order construction. No cofinality, same-host lifting or
map-extension callback is left as an assumption.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w p a
namespace CCO.UnfilteredEP
open CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (F : Charts.{u,v,w,p} B)
local notation "N₀" => CCO.TerminalHiddenHN.binaryNormalForms
  (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)
local notation "N₁" => CCO.TerminalHiddenHN.orderedNormalForms
  (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)

/-- Every finite proper unexpanded member has the SAME all-input term
normal forms. Orphan-only members are admitted by the ambient-age theorem. -/
theorem actual_proper_code_normal
    (D : FiniteHidden.{max u v w,max u v} (CoordinateLanguage B ht))
    (member : ProperFiniteCodeAge B ht D) : (N₀).Valid D.model := by
  obtain ⟨f⟩ := (proper_coordinate_ambient B ht D).mp member
  exact (N₀).valid_of_embedding f (proper_coordinate_normal B ht)

/-- Orders add no unary function or domain. Thus OLD and expanded
supports are literally equal for EVERY collection of marked roots. -/
theorem actual_order_supports_commute
    (D : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht)) :
    SupportReductCommutes (coordinateOrderExpansion B ht) (tupleScheme B ht F) D.model := by
  intro roots
  rfl

section OrderClass
variable (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct)
variable (oldAge : ∀ D, ages.oldAge D ↔ ProperFiniteCodeAge B ht D)

/-- C80–C81: EVERY allowed expanded full-code competitor is transported
to an allowed hidden expansion on the literal existing old host. The
full expanded code, including missing-partner comparisons, is retained. -/
def actual_same_host_lift
    (E : FiniteHidden.{max u v w,max u v} (CoordinateLanguage B ht))
    (member : ages.oldAge E) (generated : RootGenerated E.model (tupleScheme B ht F))
    (competitor : SameHostRepresentation (coordinateOrderExpansion B ht) (N₀)
      (tupleScheme B ht F) ages.expandedAge E) :
    SameHostLift (coordinateOrderExpansion B ht) (N₁) competitor :=
  competitor.lift ages
    (actual_proper_code_normal B ht E ((oldAge E).mp member))
    (actual_proper_code_normal B ht (competitor.host.reduct (coordinateOrderExpansion B ht).toReduct)
      ((oldAge _).mp (ages.reductMember competitor.host competitor.member)))
    generated (actual_order_supports_commute B ht F competitor.host) (N₁)

include oldAge in
/-- The lifted code fixes every visible root rather than merely choosing
an isomorphic root packet or a convenient alternative competitor. -/
theorem actual_same_host_lift_point
    (E : FiniteHidden.{max u v w,max u v} (CoordinateLanguage B ht))
    (member : ages.oldAge E) (generated : RootGenerated E.model (tupleScheme B ht F))
    (competitor : SameHostRepresentation (coordinateOrderExpansion B ht) (N₀)
      (tupleScheme B ht F) ages.expandedAge E)
    (root : Root E.model (tupleScheme B ht F)) :
    (actual_same_host_lift B ht F ages oldAge E member generated competitor).code.point root = root :=
  (actual_same_host_lift B ht F ages oldAge E member generated competitor).point_eq root

include oldAge in
/-- C77/C80–C84's exact full-code consequence. The finite cofinal host,
canonical support equivalence, EVERY-competitor SAME-host lift and all-map
full code are constructed from the actual fixed chart. Only EP of the
specified normalized hidden expansion is a remaining theorem input. -/
theorem actual_root_covered_order_code_EP
    (hiddenEP : ages.HiddenEP) :
    VisibleFullCodeEP.{max u v w,max u v,a}
      (coordinateOrderExpansion B ht) ages (N₀) (N₁) (tupleScheme B ht F) := by
  apply cofinal_finite_tuple_EP (coordinateOrderExpansion B ht) ages (N₀) (N₁) (tupleScheme B ht F)
    hiddenEP
  · intro D _
    exact actual_order_supports_commute B ht F D
  · intro D member
    obtain ⟨E,hE,generated,embedding⟩ := actual_proper_cofinal_root_hosts B ht F D
      ((oldAge D).mp member)
    exact ⟨E,(oldAge E).mpr hE,generated,embedding⟩
  · intro E member generated competitor
    exact ⟨actual_same_host_lift B ht F ages oldAge E member generated competitor⟩

end OrderClass
end
end CCO.UnfilteredEP
