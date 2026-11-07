import CCO.UnfilteredEP.ProperHiddenSupport
import CCO.UnfilteredEP.QuotientPairClosure

/-! Actual finite closed supports in the SAME proper hidden target.
Closure is finite for every finite seed set; all proper sorts are kept.
These support statements require no Ramsey or expansion property. -/

universe u v w
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.UnaryTermsReturn
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)

theorem proper_triple_closure_eq_pair_union (x y z : Values B) :
    (Target B ht).closure {x,y,z} =
      (Target B ht).closure {x,y} ∪ (Target B ht).closureAt z := by
  have hs : ({x,y,z} : Set (Values B)) = {x,y} ∪ {z} := by
    ext p
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Set.mem_union]
    exact or_assoc.symm
  rw [hs,(Target B ht).closure_union]
  rfl

theorem proper_triple_new_in_singleton {x y z a : Values B}
    (ha : a ∈ (Target B ht).closure {x,y,z})
    (hnot : a ∉ (Target B ht).closure {x,y}) :
    a ∈ (Target B ht).closureAt z := by
  rw [proper_triple_closure_eq_pair_union] at ha
  exact ha.resolve_left hnot

theorem proper_target_finite_closure (A : Set (Values B)) (hA : A.Finite) :
    ((Target B ht).closure A).Finite := by
  rw [actual_partial_closure_eq]
  letI : Finite A := hA.to_subtype
  have hf : (⋃ a : A, (Hidden B ht).closureAt a.val).Finite :=
    Set.finite_iUnion (fun a =>
      CCO.TypedOrbitFrames.original_completed_all_singleton_closures_finite
        (cloneSource B) (HF B) (cloneSAP B)
        (CCO.TerminalHiddenHN.NR2 (cloneSource B) (fullCovers B ht)) a.val)
  apply hf.subset
  intro y hy
  obtain ⟨x,hx,hxy⟩ := (Hidden B ht).mem_closure_iff_singleton.mp hy
  exact Set.mem_iUnion.mpr ⟨⟨x,hx⟩,hxy⟩

theorem proper_target_closure_proper (A : Set (Values B))
    (hA : ∀ x ∈ A, ProperSort B ht ((Target B ht).sort x)) :
    ∀ x ∈ (Target B ht).closure A, ProperSort B ht ((Target B ht).sort x) :=
  (Target B ht).closure_minimal (proper_set_closed B ht (Target B ht)) hA

/-- C58: actual proper finite generated witnesses are induced CLOSED
members of the entire age, including all generated partner coordinates. -/
theorem proper_target_closure_member (A : Set (Values B)) (hA : A.Finite)
    (hp : ∀ x ∈ A, ProperSort B ht ((Target B ht).sort x)) :
    ProperAge B ht ((Target B ht).closureStructure A) := by
  refine ⟨?_,?_⟩
  · exact CCO.TerminalHiddenHN.actualAge_of_closed
      (cloneSource B) (cloneHomogeneous B) (cloneSAP B) (fullCovers B ht)
      _ (proper_target_finite_closure B ht A hA) ((Target B ht).isClosed_closure A)
  · intro x
    exact proper_target_closure_proper B ht A hp x.val x.property

end
end CCO.UnfilteredEP
