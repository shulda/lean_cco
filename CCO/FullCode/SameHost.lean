import CCO.FullCode.SupportEquivalence
import CCO.FullCode.ExpansionRoots
import Mathlib.Logic.Equiv.Set

/-! A competing full-code expansion on fixed roots is transported onto the
EXACT old host. The marked old support equivalence is derived from FCODE. -/
universe u v
namespace CCO.FullCode
variable {L₀ L₁ : Language.{u}} (ρ : LanguageExpansion L₀ L₁)

private theorem coordinate_cast_eq {L : Language.{u}} {V : Type v}
    {C : Structure L V} {S : RootScheme L} {r s : Root C S} (h : r = s)
    {tag : S.Tag} (hr : r.tag = tag) (hs : s.tag = tag) (j : Fin (S.arity tag)) :
    r.coordinate (hr.symm ▸ j) = s.coordinate (hs.symm ▸ j) := by
  cases h
  rfl

structure SameHostRepresentation (N₀ : NormalForms L₀) (S : RootScheme L₀)
    (H₁ : FiniteHidden.{u,v} L₁ → Prop) (E : FiniteHidden.{u,v} L₀) where
  host : FiniteHidden.{u,v} L₁
  member : H₁ host
  object : Object host.model (S.lift ρ) (Root E.model S)
  oldCode : Object.Embedding N₀ (Object.full E.model S) object.toOld
  point_eq : ∀ r, oldCode.point r = r

structure SameHostLift {N₀ : NormalForms L₀} {S : RootScheme L₀}
    {H₁ : FiniteHidden.{u,v} L₁ → Prop} {E : FiniteHidden.{u,v} L₀}
    (N₁ : NormalForms L₁) (R : SameHostRepresentation ρ N₀ S H₁ E) where
  expansion : ExpansionOn ρ.toReduct H₁ E
  hidden : Structure.Embedding expansion.model R.host.model
  root_eq : ∀ r, ((expansion.rootObject ρ S).root r).map hidden = R.object.root r
  code : Object.Embedding N₁ (expansion.rootObject ρ S) R.object
  point_eq : ∀ r, code.point r = r

namespace SameHostRepresentation
variable {ρ} {N₀ : NormalForms L₀} {S : RootScheme L₀}
  {H₁ : FiniteHidden.{u,v} L₁ → Prop} {E : FiniteHidden.{u,v} L₀}

noncomputable def markedEquiv (R : SameHostRepresentation ρ N₀ S H₁ E)
    (hE : N₀.Valid E.model) (hD : N₀.Valid (R.host.model.reduct ρ.toReduct))
    (generated : RootGenerated E.model S)
    (commutes : SupportReductCommutes ρ S R.host.model) : E.Carrier ≃ R.object.support :=
  (fullSupportEquiv E.model S generated).trans
    ((R.oldCode.supportEquiv hE hD (by intro r; exact ⟨r, R.point_eq r⟩)).trans
      (Set.equivOfEq (R.object.support_reduct_eq_of_commutes commutes)).symm)

theorem markedEquiv_val (R : SameHostRepresentation ρ N₀ S H₁ E)
    (hE : N₀.Valid E.model) (hD : N₀.Valid (R.host.model.reduct ρ.toReduct))
    (generated : RootGenerated E.model S)
    (commutes : SupportReductCommutes ρ S R.host.model) (x : E.Carrier) :
    (R.markedEquiv hE hD generated commutes x).val =
      (R.oldCode.extend hE hD).point (fullSupportEquiv E.model S generated x) := by
  rfl

noncomputable def lift (ages : ExpansionAges.{u,v} ρ.toReduct)
    (R : SameHostRepresentation ρ N₀ S ages.expandedAge E)
    (hE : N₀.Valid E.model) (hD : N₀.Valid (R.host.model.reduct ρ.toReduct))
    (generated : RootGenerated E.model S)
    (commutes : SupportReductCommutes ρ S R.host.model)
    (N₁ : NormalForms L₁) : SameHostLift ρ N₁ R := by
  let e := R.markedEquiv hE hD generated commutes
  let H := R.host.induced R.object.support (R.host.model.isClosed_closure R.object.coordinates)
  let M := R.object.supportStructure.comapEquiv e
  let g : Structure.Embedding M R.host.model :=
    (R.host.model.inclusion R.object.support (R.host.model.isClosed_closure R.object.coordinates)).comp
      (R.object.supportStructure.comapEquivEmbedding e)
  let fOld : Structure.Embedding E.model (R.host.model.reduct ρ.toReduct) :=
    (R.oldCode.extend hE hD).comp (fullSupportEmbedding E.model S generated)
  have hred : M.reduct ρ.toReduct = E.model :=
    (g.reduct ρ.toReduct).source_eq_of_same_point fOld (fun x => R.markedEquiv_val hE hD generated commutes x)
  have hH : ages.expandedAge H := ages.expandedHereditary R.host R.member _ _
  have hM : ages.expandedAge ⟨E.Carrier, M, E.finite⟩ :=
    ages.expandedIsoClosed H hH E.Carrier e
  let b : ExpansionOn ρ.toReduct ages.expandedAge E := ⟨M, hred, hM⟩
  have hroot : ∀ r, ((b.rootObject ρ S).root r).map g = R.object.root r := by
    intro r
    have ht : (R.object.root r).tag = r.tag := by
      have h := R.oldCode.tag_eq r
      rw [R.point_eq r] at h
      exact h
    apply Root.ext_coordinates ht.symm
    intro j
    have hcoord := R.oldCode.extendPoint_coordinate hE hD r j
    have he := coordinate_cast_eq (congrArg R.object.toOld.root (R.point_eq r))
      (R.oldCode.tag_eq r) ht j
    have hc : R.oldCode.extendPoint hE ⟨r.coordinate j, (Object.full E.model S).coordinate_mem_support r j⟩ =
        (R.object.root r).coordinate (ht.symm ▸ j) := hcoord.trans he
    exact (R.markedEquiv_val hE hD generated commutes (r.coordinate j)).trans hc
  let c : Object.Embedding N₁ (b.rootObject ρ S) R.object := {
    point := fun r => r
    injective := Function.injective_id
    tag_eq := fun r => (congrArg Root.tag (hroot r)).symm
    equality_iff := fun r s p q => by
      rw [← hroot r, ← hroot s]
      exact equalityCode_map N₁ g _ _ p q
    unary_iff := fun U r p => by
      rw [← hroot r]
      exact unaryCode_map N₁ g U _ p
    binary_iff := fun U r s p q => by
      rw [← hroot r, ← hroot s]
      exact binaryCode_map N₁ g U _ _ p q
  }
  exact ⟨b, g, hroot, c, fun _ => rfl⟩

end SameHostRepresentation
end CCO.FullCode
