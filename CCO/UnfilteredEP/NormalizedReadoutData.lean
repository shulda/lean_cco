import CCO.UnfilteredEP.NormalizedReadoutReasonable
import CCO.UnfilteredEP.RestrictedExpansion

/-! The finite FULL relational presentation of the specified concrete
normalized hidden class. No fixed code is deleted from the language. -/

universe u v w p
namespace CCO.UnfilteredEP
open CCO CCO.FullCode CCO.APRamseyReadout CCO.CloneTupleGeometry
open CCO.TerminalHiddenHN
noncomputable section
variable (B : OwnerStage.{u,v,w}) (ht : B.Terminal) (F : Charts.{u,v,w,p} B)
variable (ages : ExpansionAges.{max u v w,max u v} (coordinateOrderExpansion B ht).toReduct)
variable (oldAge : ∀ D, ages.oldAge D ↔ ProperFiniteCodeAge B ht D)
variable (proper : ∀ D, ages.expandedAge D → ProperOrderedAge B ht D)
local notation "Γ" => actualTupleInterpretation B ht F

/-- All old finite objects receive exactly the readouts whose whole
ordered support belongs to the specified normalized hidden age. -/
def normalizedReadoutData : RealExpansionData.{u,v,w,max u v w,max u v} B.source :=
  restrictedExpansion (actualFullReadoutData B ht F)
    (fun _ a => ages.expandedAge (actualOrderedTemplate B ht F a))
    (normalized_readout_nonempty B ht F ages oldAge proper)
    (fun f b hb => normalized_readout_restrict B ht F ages f b hb)

local notation "Eₙ" => normalizedReadoutData B ht F ages oldAge proper

/-- Finite table arrows recover the exact same old map and support order. -/
def normalizedToReadout {A E : FiniteInduced (X := B.Point)}
    {a : (Eₙ).Expansion A} {b : (Eₙ).Expansion E}
    (f : (Eₙ).Embedding a b) : (Γ).ReadoutEmbedding B.homogeneous a.val b.val :=
  (Γ).relationalToReadout B.homogeneous ⟨f.old,f.unary_iff,f.binary_iff⟩

def readoutToNormalized {A E : FiniteInduced (X := B.Point)}
    {a : (Eₙ).Expansion A} {b : (Eₙ).Expansion E}
    (f : (Γ).ReadoutEmbedding B.homogeneous a.val b.val) : (Eₙ).Embedding a b := by
  let g := (Γ).readoutToRelational B.homogeneous f
  exact ⟨g.old,g.unary_iff,g.binary_iff⟩

@[simp] theorem readoutToNormalized_old {A E : FiniteInduced (X := B.Point)}
    {a : (Eₙ).Expansion A} {b : (Eₙ).Expansion E}
    (f : (Γ).ReadoutEmbedding B.homogeneous a.val b.val) :
    (readoutToNormalized B ht F ages oldAge proper f).old = f.old := rfl

theorem normalized_readout_data_reasonable : (Eₙ).Reasonable := by
  intro A E f a
  obtain ⟨b,hb,equal⟩ := normalized_readout_reasonable B ht F ages oldAge proper
    f a.val a.property
  exact ⟨⟨b,hb⟩,Subtype.ext equal⟩

/-- Actual universal-competitor hidden EP gives EP of this SAME full
finite relational presentation on one fixed old visible host. -/
theorem normalized_readout_data_EP (hiddenEP : ages.HiddenEP) : (Eₙ).EP := by
  intro A a
  obtain ⟨E,arrow⟩ := actual_relative_readout_EP B ht F ages oldAge hiddenEP
    A a.val a.property
  refine ⟨E,?_⟩
  intro b
  obtain ⟨f⟩ := arrow b.val b.property
  exact ⟨readoutToNormalized B ht F ages oldAge proper f⟩

theorem normalized_readout_data_precompact (A : FiniteInduced (X := B.Point)) :
    Finite ((Eₙ).Expansion A) := (Eₙ).finite_expansions A

end
end CCO.UnfilteredEP
