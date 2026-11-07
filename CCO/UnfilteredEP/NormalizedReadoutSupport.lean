import CCO.UnfilteredEP.ActualReadoutEP

/-! Canonical whole supports for the concrete normalized hidden age.
Every supplied expansion on one of these old supports determines exactly
one full readout; no order normalization changes a competitor. -/

set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 250000
set_option maxHeartbeats 1000000
universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
local notation "Γ" => actualTupleInterpretation B ht F

/-- The whole old hidden support, including every named intermediate
term value. Its carrier is the literal canonical support. -/
def actualOldSupport (A : FiniteInduced (X := B.Point)) :
    FiniteHidden.{max u v w,max u v} (CoordinateLanguage B ht) :=
  ⟨(Γ).support A,CoordinateModel B ht (actualTemplateRaw B ht F A),
    (actualTupleSupport_finite B ht F A).to_subtype⟩

theorem actualOldSupport_mem (A : FiniteInduced (X := B.Point)) :
    ProperFiniteCodeAge B ht (actualOldSupport B ht F A) := by
  constructor
  · change ActualAge B ht (TerminalHiddenHN.binaryDecode _ _
      (CoordinateModel B ht (actualTemplateRaw B ht F A)))
    rw [TerminalHiddenHN.binaryDecode_binaryStructure]
    exact actualTemplateRaw_mem B ht F A
  · intro x
    exact actualTupleSupport_proper B ht F A x.property

/-- The old map of supports retains exactly the original induced map. -/
def actualOldSupportMap {A E : FiniteInduced (X := B.Point)}
    (f : InducedEmbedding B.source A E) :
    Structure.Embedding (actualOldSupport B ht F A).model
      (actualOldSupport B ht F E).model :=
  (((Γ).supportEmbedding B.homogeneous f).sourceCongr
    (actualTemplateRaw_binary B ht F A).symm).targetCongr
      (actualTemplateRaw_binary B ht F E).symm

/-- A full actual hidden expansion on this fixed support is literally
the template of its own order. All non-order tables are forced by the
displayed reduct equality. -/
theorem expansionOn_actualOldSupport
    (K : FiniteHidden.{max u v w,max u v} (OrderedCoordinateLanguage B ht) → Prop)
    (proper : ∀ D, K D → ProperOrderedAge B ht D)
    (A : FiniteInduced (X := B.Point))
    (e : ExpansionOn (coordinateOrderExpansion B ht).toReduct K (actualOldSupport B ht F A)) :
    ∃ a : (Γ).ReadoutOn A, e.model = (actualOrderedTemplate B ht F a).model := by
  obtain ⟨C,o,_hC,equal⟩ := (proper e.toHidden e.member).1
  dsimp only [ExpansionOn.toHidden,actualOldSupport] at C o _hC equal
  change e.model = @OrderedCoordinateModel B ht _ C o at equal
  have oldEqual : CoordinateModel B ht C =
      CoordinateModel B ht (actualTemplateRaw B ht F A) := by
    have hh := e.reduct_eq
    rw [equal] at hh
    exact hh
  have rawEqual : C = actualTemplateRaw B ht F A := by
    have hh := congrArg (TerminalHiddenHN.binaryDecode (Sig B ht)
      (TerminalHiddenHN.sig_binary (cloneSource B) (cloneHomogeneous B)
        (cloneSAP B) (fullCovers B ht))) oldEqual
    dsimp only [CoordinateModel] at hh
    rw [TerminalHiddenHN.binaryDecode_binaryStructure,
      TerminalHiddenHN.binaryDecode_binaryStructure] at hh
    exact hh
  refine ⟨⟨o⟩,?_⟩
  exact equal.trans (congrArg (fun D => @OrderedCoordinateModel B ht _ D o) rawEqual)

/-- Existence of normalized readouts is received from genuine
reduct-surjectivity of the exact hidden expansion age. -/
theorem normalized_readout_nonempty
    (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct)
    (oldAge : ∀ D, ages.oldAge D ↔ ProperFiniteCodeAge B ht D)
    (proper : ∀ D, ages.expandedAge D → ProperOrderedAge B ht D)
    (A : FiniteInduced (X := B.Point)) :
    ∃ a : (Γ).ReadoutOn A, ages.expandedAge (actualOrderedTemplate B ht F a) := by
  obtain ⟨e⟩ := ages.reductSurjective (actualOldSupport B ht F A)
    ((oldAge _).mpr (actualOldSupport_mem B ht F A))
  obtain ⟨a,equal⟩ := expansionOn_actualOldSupport B ht F ages.expandedAge proper A e
  refine ⟨a,?_⟩
  have member := e.member
  change ages.expandedAge ⟨_,(actualOrderedTemplate B ht F a).model,_⟩
  rw [← equal]
  exact member

/-- Every actual induced old restriction stays in the same concrete
normalized hidden age, by its full hereditary/iso closure. -/
theorem normalized_readout_restrict
    (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct)
    {A E : FiniteInduced (X := B.Point)} (f : InducedEmbedding B.source A E)
    (b : (Γ).ReadoutOn E) (member : ages.expandedAge (actualOrderedTemplate B ht F b)) :
    ages.expandedAge (actualOrderedTemplate B ht F ((Γ).restrictReadout B.homogeneous f b)) :=
  hidden_member_of_embedding ages.expandedAge ages.expandedHereditary ages.expandedIsoClosed
    member (actualTemplateEmbedding B ht F ((Γ).restrictReadoutEmbedding B.homogeneous f b))

end
end CCO.UnfilteredEP
