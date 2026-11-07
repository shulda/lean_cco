import CCO.UnfilteredEP.ResetEdgeTaskIso
import CCO.UnfilteredEP.NormalizedTaskHereditary

/-! The actual complete reset edge type required by the accepted reset
EP theorem. The template is its entire generated full pair, and every
realization is a surjective full pointed isomorphism of whole supports. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1500000
universe u v w
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
open CCO.ResetOrder.Unary
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (n : Nat)
variable (J : HiddenCut B) (m : ActualResetMenu B (fullMIOfNamed B J.1 J.2))
variable (priority : LinearOrder (Sig B ht).Sorts)

/-- C37-C42 discharged on the ONE actual normalized full provider,
with no edge-type hypothesis or omitted partner coordinates. -/
theorem normalized_task_complete_reset_edge_type :
    CompleteResetEdgeType (normalizedTaskFullAge B ht n J m priority) := by
  intro A hA x y hxy hreset
  let H := pairClosure A x y
  let p := pairLeft A x y
  let q := pairRight A x y
  have hH : normalizedTaskFullAge B ht n J m priority H :=
    normalized_task_full_hereditary B ht n J m priority hA ⟨pairInclusion A x y⟩
  have hcomp : H.task.order.lt p q := hxy
  have hresetH : (actualTaskFibres B ht n J m).reset H.task.old p q :=
    ((actualTaskFibres B ht n J m).reset_natural (pairInclusion A x y).task.old p q).mp hreset
  refine ⟨{
    object := H
    mem := hH
    left := p
    right := q
    comparison := hcomp
    reset := hresetH
    generated := full_pair_generated A x y
    realizes := ?_ }⟩
  intro C hC x' y' hxy' hreset'
  let T := pairClosure C x' y'
  let p' := pairLeft C x' y'
  let q' := pairRight C x' y'
  have hT : normalizedTaskFullAge B ht n J m priority T :=
    normalized_task_full_hereditary B ht n J m priority hC ⟨pairInclusion C x' y'⟩
  have hcomp' : T.task.order.lt p' q' := hxy'
  have hresetT : (actualTaskFibres B ht n J m).reset T.task.old p' q' :=
    ((actualTaskFibres B ht n J m).reset_natural (pairInclusion C x' y').task.old p' q').mp hreset'
  obtain ⟨f,hp,hq⟩ := normalized_task_generated_edge_iso B ht n J m priority hH hT
    p q p' q' (full_pair_generated A x y) (full_pair_generated C x' y') hcomp hcomp' hresetH hresetT
  exact ⟨⟨f,hp,hq⟩⟩

end
end CCO.UnfilteredEP
