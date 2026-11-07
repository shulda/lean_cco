import CCO.UnfilteredEP.ActualSingletonSupport
import CCO.APRamseyReadout.RamseyReadout
import CCO.APRamseyReadout.VisibleJEP

/-!
# The actual block Ramsey provider is singleton-faithful

All predicates of the full code are retained. An actual one-point old map
lifts into EVERY allowed block expansion of its target, since restriction
has the unique expanded source singleton. Ramsey remains the previously
proved block Ramsey arrow, independent of order EP and automatic core.
-/

universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (F : Charts.{u,v,w,p} B)
variable (priority : LinearOrder (CoordinateLanguage B ht).Sorts)
local notation "Γ" => actualTupleInterpretation B ht F

/-- Every prescribed original map out of one singleton is a genuine
expanded embedding into the arbitrary target expansion already chosen. -/
def actual_singleton_block_embedding
    {A E : FiniteInduced (X := B.Point)}
    (point : Sigma B.Point) (singleton : ∀ x : A.vertices, x.val = point)
    (a : (Γ).BlockReadoutOn priority A) (b : (Γ).BlockReadoutOn priority E)
    (old : InducedEmbedding B.source A E) :
    (Γ).ReadoutEmbedding B.homogeneous a.val b.val := by
  letI := blockReadout_subsingleton_of_sort_injective (Γ) priority A
    (actual_singleton_support_sort_injective B ht F A point singleton)
  have h : (Γ).restrictBlockReadout priority B.homogeneous old b = a :=
    Subsingleton.elim _ _
  refine ⟨old,?_⟩
  intro x y
  have ho := congrArg (fun c : (Γ).BlockReadoutOn priority A => c.val.order) h
  change @LT.lt _ b.val.order.toLT
      (((Γ).supportEmbedding B.homogeneous old).point x)
      (((Γ).supportEmbedding B.homogeneous old).point y) ↔
    @LT.lt _ a.val.order.toLT x y
  have hrestricted : @LT.lt _ b.val.order.toLT
      (((Γ).supportEmbedding B.homogeneous old).point x)
      (((Γ).supportEmbedding B.homogeneous old).point y) ↔
    @LT.lt _ ((Γ).restrictBlockReadout priority B.homogeneous old b).val.order.toLT x y :=
    Iff.rfl
  rw [ho] at hrestricted
  exact hrestricted

@[simp] theorem actual_singleton_block_embedding_old
    {A E : FiniteInduced (X := B.Point)}
    (point : Sigma B.Point) (singleton : ∀ x : A.vertices, x.val = point)
    (a : (Γ).BlockReadoutOn priority A) (b : (Γ).BlockReadoutOn priority E)
    (old : InducedEmbedding B.source A E) :
    (actual_singleton_block_embedding B ht F priority point singleton a b old).old = old := by
  rfl

/-- Actual C26 Ramsey/JEP input remains prior to every EP application.
The singleton theorem above applies to its SAME full block readout. -/
theorem actual_singleton_provider_ramsey :
    (Γ).BlockReadoutRamsey priority B.homogeneous :=
  actual_block_readout_ramsey B ht F priority

end
end CCO.UnfilteredEP
