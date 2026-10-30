import CCO.FullCode.SameHost
import CCO.FullCode.SourceSupport
import CCO.FullCode.CofinalAge

/-! Actual fixed-host EP transfer.  Hidden EP and hidden Ramsey remain
separate.  No closed-range, source-support, normalization, root-readout or
restriction callback is added to either principal theorem. -/

universe u v a
namespace CCO.FullCode
variable {L₀ L₁ : Language.{u}} (ρ : LanguageExpansion L₀ L₁)

/-- Every fixed expanded visible source embeds in every allowed competing
full-code expansion of ONE old full-root host chosen beforehand. -/
def VisibleFullCodeEP (ages : ExpansionAges.{u,v} ρ.toReduct)
    (N₀ : NormalForms L₀) (N₁ : NormalForms L₁) (S : RootScheme L₀) : Prop :=
  ∀ (D : FiniteHidden.{u,v} L₁), ages.expandedAge D →
    ∀ (A : Type a) (O : Object D.model (S.lift ρ) A),
      ∃ B : FiniteHidden.{u,v} L₀, ages.oldAge B ∧ RootGenerated B.model S ∧
        ∀ R : SameHostRepresentation ρ N₀ S ages.expandedAge B,
          Nonempty (Object.Embedding N₁ O R.object)

/-- C32--C39.  The two remaining application contracts are precisely actual
cofinality and the source's universal SAME-host contract.  The hidden source,
OLD-root normalization, reasonable extension, added-function image closure,
legal restriction and reverse-FCODE map are all constructed in this proof. -/
theorem cofinal_tuple_EP (ages : ExpansionAges.{u,v} ρ.toReduct)
    (N₀ : NormalForms L₀) (N₁ : NormalForms L₁) (S : RootScheme L₀)
    (hiddenEP : ages.HiddenEP) (commutes : ages.SupportsCommute S)
    (cofinal : CofinalRootHosts ages.oldAge S)
    (sameHost : ∀ (B : FiniteHidden.{u,v} L₀), ages.oldAge B → RootGenerated B.model S →
      ∀ R : SameHostRepresentation ρ N₀ S ages.expandedAge B, Nonempty (SameHostLift ρ N₁ R)) :
    VisibleFullCodeEP.{u,v,a} ρ ages N₀ N₁ S := by
  intro D member A O
  obtain ⟨W, hW, generatedW, witness⟩ :=
    ages.normalized_visible_witness S hiddenEP commutes D member O
  obtain ⟨B, hB, generatedB, ⟨j⟩⟩ := cofinal W hW
  refine ⟨B, hB, generatedB, ?_⟩
  intro R
  obtain ⟨lift⟩ := sameHost B hB generatedB R
  let w := ages.restrictGenerated S commutes lift.expansion j generatedW
  let inclusion := ages.restrictGeneratedEmbedding S commutes lift.expansion j generatedW
  obtain ⟨u⟩ := witness w
  exact ⟨lift.code.comp
    (lift.expansion.fromHiddenOnOldRoots ρ S N₁ O (inclusion.comp u))⟩

/-- C40--C43.  Every abstract application contract is discharged from the
ambient root-covered full-code setting.  The only support compatibility is
the source's A07 actual marked reduct equation; no HostRoute or expanded
closure assumption remains.  Expanded NF validity is retained from A02. -/
theorem ambient_root_covered_full_code_EP (ages : ExpansionAges.{u,v} ρ.toReduct)
    (N₀ : NormalForms L₀) (N₁ : NormalForms L₁) (S : RootScheme L₀)
    (validOld : ∀ D : FiniteHidden.{u,v} L₀, ages.oldAge D → N₀.Valid D.model)
    (_validExpanded : ∀ D : FiniteHidden.{u,v} L₁, ages.expandedAge D → N₁.Valid D.model)
    {V : Type v} (P : Structure L₀ V)
    (ambient : IsAmbientAge ages.oldAge P) (cover : RootCovered P S)
    (validRootForms : RootNormalFormsValid N₀ P S)
    (hiddenEP : ages.HiddenEP) (commutes : ages.SupportsCommute S) :
    VisibleFullCodeEP.{u,v,a} ρ ages N₀ N₁ S := by
  apply cofinal_tuple_EP ρ ages N₀ N₁ S hiddenEP commutes
    (root_cover_cofinal_rootForms P S N₀ validRootForms ambient cover)
  intro B hB generated R
  exact ⟨R.lift ages (validOld B hB)
    (validOld (R.host.reduct ρ.toReduct) (ages.reductMember R.host R.member))
    generated (commutes R.host R.member) N₁⟩

end CCO.FullCode
