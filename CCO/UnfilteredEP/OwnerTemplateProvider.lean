import CCO.UnfilteredEP.OwnerEmbedding
import CCO.UnfilteredEP.OwnerMarkingLift
import CCO.UnfilteredEP.FullBlockReadout
import CCO.UnfilteredEP.SingletonFaithful
import CCO.TerminalHiddenHN.UnaryLift

/-! Actual FULL block-code Ramsey objects over the original owner age.
Every object remembers a whole actual terminal lift. The permitted maps
are exactly the existing full relational embeddings on the same old map. -/

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

abbrev ownerLiftedBlockData :=
  UnaryLift.data (OwnerStage.historyReduct history)
    (actualFullBlockReadoutData D terminal F priority)

abbrev OwnerProviderObject :=
  Σ A : FiniteInduced (X := B.Point),
    Σ L : UnaryLift.Lift (OwnerStage.historyReduct history) A,
      (actualFullBlockReadoutData D terminal F priority).Expansion L.object

abbrev ownerProviderExpansion (A : OwnerProviderObject history terminal F priority) :
    (ownerLiftedBlockData history terminal F priority).Expansion A.1 :=
  UnaryLift.fromLift _ _ A.2.1 A.2.2

/-- The generic provider's condition is actual FULL-code map existence,
not a new Ramsey or EP premise. Its old map is fixed in the condition. -/
def ownerTemplateProvider : (ownerFiniteAge B).RamseyProvider (ownerTemplate history) where
  Obj := OwnerProviderObject history terminal F priority
  old A := A.1
  marking A := reductMarkingOfLift (OwnerStage.historyReduct history) A.2.1
  allowed A E f := ∃ g : (ownerLiftedBlockData history terminal F priority).Embedding
    (ownerProviderExpansion history terminal F priority A)
    (ownerProviderExpansion history terminal F priority E),
    ∀ x, g.old.toEmbedding x = f.old.toFun x
  id_allowed A := by
    refine ⟨{
      old := ⟨Function.Embedding.refl _,fun _ => rfl,fun _ _ => rfl⟩
      unary_iff := fun _ _ => Iff.rfl
      binary_iff := fun _ _ _ => Iff.rfl },fun _ => rfl⟩
  comp_allowed g f hg hf := by
    obtain ⟨rg,hrg⟩ := hg
    obtain ⟨rf,hrf⟩ := hf
    refine ⟨rg.comp rf,?_⟩
    intro x
    change rg.old.toEmbedding (rf.old.toEmbedding x) = g.old.toFun (f.old.toFun x)
    rw [hrf,hrg]

/-- A real FULL expanded map induces precisely its old marked map. -/
def ownerProviderEmbeddingOfReal
    {A E : OwnerProviderObject history terminal F priority}
    (g : (ownerLiftedBlockData history terminal F priority).Embedding
      (ownerProviderExpansion history terminal F priority A)
      (ownerProviderExpansion history terminal F priority E)) :
    (ownerTemplateProvider history terminal F priority).Embedding A E :=
  ⟨{
    old := ownerEmbeddingOfInduced B g.old
    labels x := UnaryLift.terminal_sorts (OwnerStage.historyReduct history)
      (actualFullBlockReadoutData D terminal F priority) A.2.1 E.2.1 g x },
    ⟨g,fun _ => rfl⟩⟩

/-- The allowed-map witness retains the exact point function. -/
def ownerProviderEmbeddingToReal
    {A E : OwnerProviderObject history terminal F priority}
    (f : (ownerTemplateProvider history terminal F priority).Embedding A E) :
    (ownerLiftedBlockData history terminal F priority).Embedding
      (ownerProviderExpansion history terminal F priority A)
      (ownerProviderExpansion history terminal F priority E) := f.property.choose

theorem ownerProviderEmbeddingToReal_point
    {A E : OwnerProviderObject history terminal F priority}
    (f : (ownerTemplateProvider history terminal F priority).Embedding A E) (x : A.1.vertices) :
    (ownerProviderEmbeddingToReal history terminal F priority f).old.toEmbedding x = f.val.old.toFun x :=
  f.property.choose_spec x

theorem ownerProviderEmbeddingOfReal_toReal
    {A E : OwnerProviderObject history terminal F priority}
    (f : (ownerTemplateProvider history terminal F priority).Embedding A E) :
    ownerProviderEmbeddingOfReal history terminal F priority
      (ownerProviderEmbeddingToReal history terminal F priority f) = f := by
  apply FiniteAge.RamseyProvider.Embedding.ext
  funext x
  exact ownerProviderEmbeddingToReal_point history terminal F priority f x

/-- Composition in both presentations is the identical old point map. -/
theorem ownerProviderEmbeddingOfReal_comp
    {A E C : OwnerProviderObject history terminal F priority}
    (g : (ownerLiftedBlockData history terminal F priority).Embedding
      (ownerProviderExpansion history terminal F priority E)
      (ownerProviderExpansion history terminal F priority C))
    (f : (ownerTemplateProvider history terminal F priority).Embedding A E) :
    ownerProviderEmbeddingOfReal history terminal F priority
      (g.comp (ownerProviderEmbeddingToReal history terminal F priority f)) =
    (ownerProviderEmbeddingOfReal history terminal F priority g).comp f := by
  apply FiniteAge.RamseyProvider.Embedding.ext
  funext x
  change g.old.toEmbedding
    ((ownerProviderEmbeddingToReal history terminal F priority f).old.toEmbedding x) = _
  rw [ownerProviderEmbeddingToReal_point]
  rfl

end
end CCO.UnfilteredEP
