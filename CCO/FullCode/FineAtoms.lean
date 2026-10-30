import CCO.FullCode.CofinalEP

/-! Original fine atoms are an EXPLICIT application gate. They are not
freely added predicates, and no particular MI/MR definability is inferred. -/
universe u v a b c d
namespace CCO.FullCode
variable {L : Language.{u}} {V : Type v} {W : Type a}
  {C : Structure L V} {D : Structure L W} {S : RootScheme L}
  {A : Type b} {B : Type c} {F : Type d} {N : NormalForms L}

def FineFaithfulness (O : Object C S A) (P : Object D S B)
    (source : F → A → A → Prop) (target : F → B → B → Prop) : Prop :=
  ∀ f : Object.Embedding N O P, ∀ R x y,
    target R (f.point x) (f.point y) ↔ source R x y

structure FineEmbedding (O : Object C S A) (P : Object D S B)
    (source : F → A → A → Prop) (target : F → B → B → Prop) where
  code : Object.Embedding N O P
  fine_iff : ∀ R x y, target R (code.point x) (code.point y) ↔ source R x y

section Expansion
variable {L₀ L₁ : Language.{u}} (ρ : LanguageExpansion L₀ L₁)
  (ages : ExpansionAges.{u,v} ρ.toReduct) (N₀ : NormalForms L₀)
  (N₁ : NormalForms L₁) (S₀ : RootScheme L₀)

/-- The actual fixed-host full-code EP map also preserves and reflects every
supplied original fine atom. The host is still chosen BEFORE the competitor.
The sole additional premise is precisely source A11(iv)/D12 faithfulness. -/
theorem cofinal_tuple_EP_with_fine_atoms
    (ep : VisibleFullCodeEP.{u,v,b} ρ ages N₀ N₁ S₀)
    (D₁ : FiniteHidden.{u,v} L₁) (member : ages.expandedAge D₁)
    (O : Object D₁.model (S₀.lift ρ) A) (source : F → A → A → Prop)
    (target : ∀ B₀ : FiniteHidden.{u,v} L₀,
      SameHostRepresentation ρ N₀ S₀ ages.expandedAge B₀ →
        F → Root B₀.model S₀ → Root B₀.model S₀ → Prop)
    (faithful : ∀ B₀ R, FineFaithfulness (N := N₁) O R.object source (target B₀ R)) :
    ∃ B₀ : FiniteHidden.{u,v} L₀, ages.oldAge B₀ ∧ RootGenerated B₀.model S₀ ∧
      ∀ R : SameHostRepresentation ρ N₀ S₀ ages.expandedAge B₀,
        Nonempty (FineEmbedding (N := N₁) O R.object source (target B₀ R)) := by
  obtain ⟨B₀, hB, generated, all⟩ := ep D₁ member A O
  refine ⟨B₀, hB, generated, ?_⟩
  intro R
  obtain ⟨f⟩ := all R
  exact ⟨⟨f, faithful B₀ R f⟩⟩

/-- The ambient corollary DISCHARGES the full-code reconstruction,
cofinality, SAME-host and reverse-embedding contracts. Original fine-atom
faithfulness remains exactly the stated application input. -/
theorem ambient_root_covered_EP_with_fine_atoms
    (validOld : ∀ D₀ : FiniteHidden.{u,v} L₀, ages.oldAge D₀ → N₀.Valid D₀.model)
    (validExpanded : ∀ D₁ : FiniteHidden.{u,v} L₁, ages.expandedAge D₁ → N₁.Valid D₁.model)
    {P : Type v} (ambientModel : Structure L₀ P)
    (ambient : IsAmbientAge ages.oldAge ambientModel) (cover : RootCovered ambientModel S₀)
    (validRootForms : RootNormalFormsValid N₀ ambientModel S₀)
    (hiddenEP : ages.HiddenEP) (commutes : ages.SupportsCommute S₀)
    (D₁ : FiniteHidden.{u,v} L₁) (member : ages.expandedAge D₁)
    (O : Object D₁.model (S₀.lift ρ) A) (source : F → A → A → Prop)
    (target : ∀ B₀ : FiniteHidden.{u,v} L₀,
      SameHostRepresentation ρ N₀ S₀ ages.expandedAge B₀ →
        F → Root B₀.model S₀ → Root B₀.model S₀ → Prop)
    (faithful : ∀ B₀ R, FineFaithfulness (N := N₁) O R.object source (target B₀ R)) :
    ∃ B₀ : FiniteHidden.{u,v} L₀, ages.oldAge B₀ ∧ RootGenerated B₀.model S₀ ∧
      ∀ R : SameHostRepresentation ρ N₀ S₀ ages.expandedAge B₀,
        Nonempty (FineEmbedding (N := N₁) O R.object source (target B₀ R)) := by
  apply cofinal_tuple_EP_with_fine_atoms ρ ages N₀ N₁ S₀
    (ambient_root_covered_full_code_EP ρ ages N₀ N₁ S₀ validOld validExpanded ambientModel
      ambient cover validRootForms hiddenEP commutes) D₁ member O source target faithful

end Expansion
end CCO.FullCode
