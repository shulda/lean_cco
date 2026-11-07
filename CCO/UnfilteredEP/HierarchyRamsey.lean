import CCO.UnfilteredEP.HierarchyFixedMaps
import CCO.FullCode.ExpandedRestriction
import CCO.FullCode.ExpansionSetting

/-!
# B064 C45--C46: Ramsey, JEP and heredity of the SAME normalized age

The ALL-orders actual proper hidden class supplies the arrows. Each target
host is normalized on its own entire carrier, and every embedding from a
fixed source keeps its literal point map. No partially ordered intermediate
class, hidden EP or unary core conclusion is used.
-/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 900000
universe u v w z
namespace CCO.UnfilteredEP
open CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.FullCode
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)

private theorem orderedModel_order_injective {V : Type z}
    (C : CCO.UnarySupport.Structure (Sig B ht) V) (o p : LinearOrder V)
    (h : @OrderedCoordinateModel B ht V C o = @OrderedCoordinateModel B ht V C p) : o = p := by
  apply LinearOrder.ext_lt
  intro x y
  have he := congrArg (fun M : Structure (OrderedCoordinateLanguage B ht) V =>
    M.binary (.inr (C.sort x,C.sort y)) x y) h
  simpa only [OrderedCoordinateModel,CCO.TerminalHiddenHN.orderedStructure,true_and] using Iff.of_eq he

/-- C46. Every actual induced closed subobject inherits the same
normalized order; this also covers arbitrary finite carrier copies. -/
theorem normalized_proper_of_embedding
    {A D : FiniteHidden.{max u v w,z} (OrderedCoordinateLanguage B ht)}
    (hD : NormalizedProperAge B ht priority D)
    (e : Structure.Embedding A.model D.model) : NormalizedProperAge B ht priority A := by
  let P := normalizedPresentation B ht priority hD
  have hA := proper_ordered_of_embedding B ht
    (normalizedProperAge_to_proper B ht priority hD) e
  obtain ⟨C,o,hC,heq⟩ := hA.1
  have proper : ∀ x, ProperSort B ht (C.sort x) := by
    intro x
    have hx := hA.2 x
    rw [heq] at hx
    exact hx
  let e0 := FullEmbedding.castModels e heq P.model_eq
  let e1 := normalizedOrderedEmbedding B ht priority C proper hC P.proper P.actual o P.order e0
  let e2 := FullEmbedding.castModels e1 rfl
    (congrArg (fun o => @OrderedCoordinateModel B ht D.Carrier P.raw o) P.fixed)
  have same : normalizedCoordinateModel B ht priority C proper hC o =
      @OrderedCoordinateModel B ht A.Carrier C o :=
    e2.source_eq_of_same_point e0 (by
      intro x
      simp only [e2,e1,FullEmbedding.castModels_point,normalizedOrderedEmbedding_point])
  exact ⟨C,o,hC,proper,orderedModel_order_injective B ht C _ _ same,heq⟩

theorem normalized_proper_hereditary :
    HereditaryHidden (NormalizedProperAge.{u,v,w,z} B ht priority) := by
  intro D hD T hT
  exact normalized_proper_of_embedding B ht priority hD (D.model.inclusion T hT)

theorem normalized_proper_isoClosed :
    HiddenIsoClosed (NormalizedProperAge.{u,v,w,z} B ht priority) := by
  intro D hD V _ e
  exact normalized_proper_of_embedding B ht priority hD (D.model.comapEquivEmbedding e)

/-- C45. One common actual normalized Ramsey provider, obtained BEFORE
any order-EP, tuple-EP or finite-template core application. -/
theorem normalized_proper_ramsey :
    HasHiddenRamsey (NormalizedProperAge.{u,v,w,z} B ht priority) := by
  intro A D hA hD n hn
  obtain ⟨E,hE,arrow⟩ := proper_ordered_ramsey B ht A D
    (normalizedProperAge_to_proper B ht priority hA)
    (normalizedProperAge_to_proper B ht priority hD) n hn
  obtain ⟨C,o,hC,he⟩ := hE.1
  have proper : ∀ x, ProperSort B ht (C.sort x) := by
    intro x
    have hx := hE.2 x
    rw [he] at hx
    exact hx
  let N := normalizedHiddenObject B ht priority C proper hC o
  let liftA := fun f : Structure.Embedding A.model E.model =>
    fixedIntoNormalizedHost B ht priority hA C proper hC o
      (FullEmbedding.castModels f rfl he)
  let liftD := fun f : Structure.Embedding D.model E.model =>
    fixedIntoNormalizedHost B ht priority hD C proper hC o
      (FullEmbedding.castModels f rfl he)
  refine ⟨N,normalizedHiddenObject_mem B ht priority C proper hC o,?_⟩
  intro color
  obtain ⟨g,shade,hg⟩ := arrow (fun f => color (liftA f))
  refine ⟨liftD g,shade,?_⟩
  intro f
  have heq : (liftD g).comp f = liftA (g.comp f) := by
    apply Structure.Embedding.ext
    intro x
    simp only [liftA,liftD,Structure.Embedding.comp,fixedIntoNormalizedHost_point,
      FullEmbedding.castModels_point,Function.comp_apply]
  exact (congrArg color heq).trans (hg f)

/-- C45. JEP is supplied by the SAME full proper age and SAME actual
normalization, with both prescribed source point maps retained. -/
theorem normalized_proper_jep :
    FullJointEmbedding (OrderedCoordinateLanguage B ht)
      (NormalizedProperAge.{u,v,w,z} B ht priority) := by
  intro A D hA hD
  obtain ⟨E,hE,⟨e⟩,⟨f⟩⟩ := proper_ordered_jep B ht A D
    (normalizedProperAge_to_proper B ht priority hA)
    (normalizedProperAge_to_proper B ht priority hD)
  obtain ⟨C,o,hC,he⟩ := hE.1
  have proper : ∀ x, ProperSort B ht (C.sort x) := by
    intro x
    have hx := hE.2 x
    rw [he] at hx
    exact hx
  refine ⟨normalizedHiddenObject B ht priority C proper hC o,
    normalizedHiddenObject_mem B ht priority C proper hC o,?_,?_⟩
  · exact ⟨fixedIntoNormalizedHost B ht priority hA C proper hC o
      (FullEmbedding.castModels e rfl he)⟩
  · exact ⟨fixedIntoNormalizedHost B ht priority hD C proper hC o
      (FullEmbedding.castModels f rfl he)⟩

end
end CCO.UnfilteredEP
