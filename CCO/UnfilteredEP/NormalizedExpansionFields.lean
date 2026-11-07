import CCO.UnfilteredEP.HierarchyFixedMaps
import CCO.UnfilteredEP.RootCoverage
import CCO.FullCode.ExpansionSetting
import CCO.TerminalHiddenHN.FiniteOrderExtension

/-! Concrete expansion-age fields for the actual synchronized hierarchy.
Each old map extends on the same carrier; its arbitrary order extension
is normalized only after the entire source order is fixed. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1200000
universe u v w z
namespace CCO.UnfilteredEP
open CCO CCO.APRamseyReadout CCO.CloneTupleGeometry CCO.FullCode
noncomputable section

/-- A finite language on a finite carrier has finitely many complete
partial-function and relation tables. -/
theorem finite_fullCode_structures (L : Language.{u}) (V : Type v) [Finite V] :
    Finite (Structure L V) := by
  apply Finite.of_injective
    (fun M : Structure L V => (M.sort,M.func,M.unary,M.binary))
  intro M N equal
  exact Structure.ext_data (congrArg (fun t => t.1) equal)
    (congrArg (fun t => t.2.1) equal) (congrArg (fun t => t.2.2.1) equal)
    (congrArg (fun t => t.2.2.2) equal)

theorem finite_expansionOn {L₀ L₁ : Language.{u}} (ρ : Reduct L₀ L₁)
    (K : FiniteHidden.{u,v} L₁ → Prop) (D : FiniteHidden.{u,v} L₀) :
    Finite (ExpansionOn ρ K D) := by
  let : Finite D.Carrier := D.finite
  let : Finite (Structure L₁ D.Carrier) := finite_fullCode_structures L₁ D.Carrier
  apply Finite.of_injective (fun e : ExpansionOn ρ K D => e.model)
  intro e f equal
  cases e
  cases f
  cases equal
  rfl

variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal)
variable (priority : LinearOrder (Sig B ht).Sorts)

theorem proper_finite_code_hereditary : HereditaryHidden (ProperFiniteCodeAge B ht) := by
  intro D hD T hT
  obtain ⟨e⟩ := (proper_coordinate_ambient B ht D).mp hD
  exact (proper_coordinate_ambient B ht (D.induced T hT)).mpr
    ⟨e.comp (D.model.inclusion T hT)⟩

/-- Forgetting only the order symbols of the actual normalized class
returns exactly the whole proper old age. -/
theorem normalized_reduct_member
    (D : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht))
    (member : NormalizedProperAge B ht priority D) :
    ProperFiniteCodeAge B ht (D.reduct (coordinateOrderExpansion B ht).toReduct) := by
  let P := normalizedPresentation B ht priority member
  constructor
  · change ActualAge B ht (TerminalHiddenHN.binaryDecode _ _
      (D.model.reduct (coordinateOrderExpansion B ht).toReduct))
    rw [P.model_eq]
    change ActualAge B ht (TerminalHiddenHN.binaryDecode _ _ (CoordinateModel B ht P.raw))
    rw [TerminalHiddenHN.binaryDecode_binaryStructure]
    exact P.actual
  · intro x
    change ProperSort B ht (D.model.sort x)
    rw [P.model_eq]
    exact P.proper x

/-- Normalizing an arbitrary order gives a genuine expansion on the
literal carrier of every old proper object. -/
theorem normalized_reduct_surjective
    (D : FiniteHidden.{max u v w,max u v} (CoordinateLanguage B ht))
    (member : ProperFiniteCodeAge B ht D) :
    Nonempty (ExpansionOn (coordinateOrderExpansion B ht).toReduct
      (NormalizedProperAge B ht priority) D) := by
  let : Finite D.Carrier := D.finite
  let C := TerminalHiddenHN.binaryDecode (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) D.model
  obtain ⟨o,normalized⟩ := proper_normalized_expansion_exists B ht priority C member.2 member.1
  exact ⟨⟨@OrderedCoordinateModel B ht _ C o,
    TerminalHiddenHN.binaryStructure_binaryDecode _ _ D.model,normalized⟩⟩

/-- Extend the whole normalized source along ANY prescribed full old
map, retaining that same point map after actual normalization. -/
theorem normalized_expansion_reasonable :
    ReasonableExpansion (coordinateOrderExpansion B ht).toReduct
      (ProperFiniteCodeAge B ht) (NormalizedProperAge B ht priority) := by
  intro A D _hA hD f a
  let P := normalizedPresentation B ht priority a.member
  let C := TerminalHiddenHN.binaryDecode (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) D.model
  have oldSource : CoordinateModel B ht P.raw = A.model := by
    have hh := a.reduct_eq
    have pEq : a.model = @OrderedCoordinateModel B ht A.Carrier P.raw P.order := P.model_eq
    rw [pEq] at hh
    exact hh
  have oldTarget : CoordinateModel B ht C = D.model :=
    TerminalHiddenHN.binaryStructure_binaryDecode _ _ D.model
  let binary := (f.sourceCongr oldSource.symm).targetCongr oldTarget.symm
  let raw := TerminalHiddenHN.binaryEmbeddingInverse (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) binary
  let : Finite D.Carrier := D.finite
  let : LinearOrder A.Carrier := P.order
  obtain ⟨o,comparisons⟩ := TerminalHiddenHN.finite_linearOrder_extension f.point f.injective
  let : LinearOrder D.Carrier := o
  let ordered : CCO.UnaryHN.Raw.OrderedEmbedding P.raw C := ⟨raw,comparisons⟩
  let full := (TerminalHiddenHN.orderedEmbedding (Sig B ht)
    (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
      (cloneSAP B) (fullCovers B ht)) ordered).sourceCongr P.model_eq.symm
  let b : ExpansionOn (coordinateOrderExpansion B ht).toReduct
      (NormalizedProperAge B ht priority) D := {
    model := normalizedCoordinateModel B ht priority C hD.2 hD.1 o
    reduct_eq := oldTarget
    member := normalizedHiddenObject_mem B ht priority C hD.2 hD.1 o }
  refine ⟨b,fixedIntoNormalizedHost B ht priority a.member C hD.2 hD.1 o full,?_⟩
  intro x
  rw [fixedIntoNormalizedHost_point]
  rfl

end
end CCO.UnfilteredEP
