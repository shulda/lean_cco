import CCO.FullCode.ExpansionSetting

/-! Construct the actual hidden expanded support of a visible source, then
choose and normalize its hidden EP witness before choosing any competitor. -/

universe u v a
namespace CCO.FullCode
variable {L₀ L₁ : Language.{u}} {ρ : LanguageExpansion L₀ L₁}

namespace ExpansionAges
variable (E : ExpansionAges.{u,v} ρ.toReduct)

theorem normalized_visible_witness (S : RootScheme L₀)
    (hiddenEP : E.HiddenEP) (commutes : E.SupportsCommute S)
    (D : FiniteHidden.{u,v} L₁) (member : E.expandedAge D)
    {A : Type a} (O : Object D.model (S.lift ρ) A) :
    ∃ W : FiniteHidden.{u,v} L₀, E.oldAge W ∧ RootGenerated W.model S ∧
      ∀ w : ExpansionOn ρ.toReduct E.expandedAge W,
        Nonempty (Structure.Embedding O.supportStructure w.model) := by
  let H := D.support O
  have hH : E.expandedAge H := support_in_hidden_age E.expandedHereditary D member O
  let H₀ := H.reduct ρ.toReduct
  have hH₀ : E.oldAge H₀ := E.reductMember H hH
  let source : ExpansionOn ρ.toReduct E.expandedAge H₀ := ⟨O.supportStructure, rfl, hH⟩
  have generated : RootGenerated H₀.model S :=
    O.reduct_support_rootGenerated (commutes D member)
  obtain ⟨W, hW, witness⟩ := hiddenEP H₀ hH₀ source
  obtain ⟨hW₀, generatedW₀, witnessW₀⟩ := E.normalized_witness source S generated W hW witness
  exact ⟨E.normalized W S, hW₀, generatedW₀, witnessW₀⟩

end ExpansionAges
end CCO.FullCode
