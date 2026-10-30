import CCO.FullCode.FiniteHidden
import CCO.FullCode.ExpandedRestriction
import CCO.FullCode.LanguageExpansion
import CCO.FullCode.SupportReduct

/-! Actual finite expansion ages.  Heredity and reasonableness are the
source's stated class hypotheses.  Closure of a chosen old image in an
arbitrary expansion is *derived*, never part of these class hypotheses. -/

universe u v
namespace CCO.FullCode
variable {L₀ L₁ : Language.{u}}

def FiniteHidden.reduct (D : FiniteHidden.{u,v} L₁) (ρ : Reduct L₀ L₁) :
    FiniteHidden.{u,v} L₀ := ⟨D.Carrier, D.model.reduct ρ, D.finite⟩

def HiddenIsoClosed {L : Language.{u}} (H : FiniteHidden.{u,v} L → Prop) : Prop :=
  ∀ (D : FiniteHidden.{u,v} L), H D → ∀ (V : Type v) [Finite V] (e : V ≃ D.Carrier),
    H ⟨V, D.model.comapEquiv e, inferInstance⟩

structure ExpansionOn (ρ : Reduct L₀ L₁)
    (H₁ : FiniteHidden.{u,v} L₁ → Prop) (D : FiniteHidden.{u,v} L₀) where
  model : Structure L₁ D.Carrier
  reduct_eq : model.reduct ρ = D.model
  member : H₁ ⟨D.Carrier, model, D.finite⟩

def ExpansionOn.toHidden {ρ : Reduct L₀ L₁} {H₁ : FiniteHidden.{u,v} L₁ → Prop}
    {D : FiniteHidden.{u,v} L₀} (d : ExpansionOn ρ H₁ D) : FiniteHidden.{u,v} L₁ :=
  ⟨D.Carrier, d.model, D.finite⟩

def ReasonableExpansion (ρ : Reduct L₀ L₁)
    (H₀ : FiniteHidden.{u,v} L₀ → Prop) (H₁ : FiniteHidden.{u,v} L₁ → Prop) : Prop :=
  ∀ (A B : FiniteHidden.{u,v} L₀), H₀ A → H₀ B →
    ∀ (f : Structure.Embedding A.model B.model) (a : ExpansionOn ρ H₁ A),
      ∃ b : ExpansionOn ρ H₁ B, ∃ g : Structure.Embedding a.model b.model,
        ∀ x, g.point x = f.point x

structure ExpansionAges (ρ : Reduct L₀ L₁) where
  oldAge : FiniteHidden.{u,v} L₀ → Prop
  expandedAge : FiniteHidden.{u,v} L₁ → Prop
  oldHereditary : HereditaryHidden oldAge
  expandedHereditary : HereditaryHidden expandedAge
  expandedIsoClosed : HiddenIsoClosed expandedAge
  reductMember : ∀ D, expandedAge D → oldAge (D.reduct ρ)
  reductSurjective : ∀ D, oldAge D → Nonempty (ExpansionOn ρ expandedAge D)
  reasonable : ReasonableExpansion ρ oldAge expandedAge
  precompact : ∀ D, oldAge D → Finite (ExpansionOn ρ expandedAge D)

namespace ExpansionAges
variable {ρ : Reduct L₀ L₁} (E : ExpansionAges.{u,v} ρ)

def Witness {A : FiniteHidden.{u,v} L₀}
    (a : ExpansionOn ρ E.expandedAge A) (D : FiniteHidden.{u,v} L₀) : Prop :=
  ∀ d : ExpansionOn ρ E.expandedAge D, Nonempty (Structure.Embedding a.model d.model)

def HiddenEP : Prop :=
  ∀ (A : FiniteHidden.{u,v} L₀), E.oldAge A →
    ∀ a : ExpansionOn ρ E.expandedAge A,
      ∃ D : FiniteHidden.{u,v} L₀, E.oldAge D ∧ E.Witness a D

def normalized (_E : ExpansionAges.{u,v} ρ) (D : FiniteHidden.{u,v} L₀)
    (S : RootScheme L₀) : FiniteHidden.{u,v} L₀ :=
  D.induced (oldRootSupport D.model S)
    (D.model.isClosed_closure (Object.full D.model S).coordinates)

/-- C48--C50.  The old-root-generated D₀ remains a witness for the fixed
expanded source.  The source's WHOLE old support is used, and every supplied
D₀ expansion is extended by reasonableness before factoring its witness map. -/
theorem normalized_witness {A : FiniteHidden.{u,v} L₀}
    (a : ExpansionOn ρ E.expandedAge A) (S : RootScheme L₀)
    (generated : RootGenerated A.model S)
    (D : FiniteHidden.{u,v} L₀) (hD : E.oldAge D) (witness : E.Witness a D) :
    E.oldAge (E.normalized D S) ∧
    RootGenerated (E.normalized D S).model S ∧
    E.Witness a (E.normalized D S) := by
  have hD₀ : E.oldAge (E.normalized D S) :=
    E.oldHereditary D hD (oldRootSupport D.model S)
      (D.model.isClosed_closure (Object.full D.model S).coordinates)
  refine ⟨hD₀, oldRootStructure_generated D.model S, ?_⟩
  intro d₀
  obtain ⟨d, j, marked⟩ := E.reasonable (E.normalized D S) D hD₀ hD
    (oldRootInclusion D.model S) d₀
  obtain ⟨f⟩ := witness d
  have gen : RootGenerated (a.model.reduct ρ) S := by
    rw [a.reduct_eq]
    exact generated
  have hold : Set.range f.point ⊆ oldRootSupport D.model S := by
    have h := (f.reduct ρ).range_subset_oldRootSupport S gen
    change Set.range f.point ⊆ oldRootSupport (d.model.reduct ρ) S at h
    rw [d.reduct_eq] at h
    exact h
  refine ⟨f.factor j ?_⟩
  intro y hy
  exact ⟨⟨y, hold hy⟩, marked _⟩

/-- Actual induced restriction and transport give an allowed expansion on
the fixed old source carrier, once expanded closure has been established. -/
noncomputable def restrictOn {D B : FiniteHidden.{u,v} L₀}
    (b : ExpansionOn ρ E.expandedAge B) (j : Structure.Embedding D.model B.model)
    (closed : b.model.IsClosed (Set.range j.point)) : ExpansionOn ρ E.expandedAge D := by
  classical
  let jred := j.targetCongr b.reduct_eq.symm
  let iso : D.Carrier ≃ Set.range j.point := Equiv.ofBijective
    (fun x => ⟨j.point x, ⟨x, rfl⟩⟩)
    ⟨fun x y h => j.injective (congrArg Subtype.val h),
      by rintro ⟨y, ⟨x, rfl⟩⟩; exact ⟨x, rfl⟩⟩
  refine ⟨b.model.pullback j.point j.injective closed, ?_, ?_⟩
  · exact b.model.pullback_reduct_eq ρ D.model jred closed
  · have hmember := E.expandedHereditary b.toHidden b.member (Set.range j.point) closed
    exact E.expandedIsoClosed (b.toHidden.induced (Set.range j.point) closed)
      hmember D.Carrier iso

def restrictOnEmbedding {D B : FiniteHidden.{u,v} L₀}
    (b : ExpansionOn ρ E.expandedAge B) (j : Structure.Embedding D.model B.model)
    (closed : b.model.IsClosed (Set.range j.point)) :
    Structure.Embedding (E.restrictOn b j closed).model b.model :=
  b.model.pullbackEmbedding j.point j.injective closed

end ExpansionAges

namespace ExpansionAges
variable {ρ : LanguageExpansion L₀ L₁} (E : ExpansionAges.{u,v} ρ.toReduct)

def SupportsCommute (S : RootScheme L₀) : Prop :=
  ∀ D : FiniteHidden.{u,v} L₁, E.expandedAge D → SupportReductCommutes ρ S D.model

/-- C51/C36: legal restriction is CONSTRUCTED for every competing expansion,
from the actual full-code support/reduct hypothesis on all allowed objects. -/
noncomputable def restrictGenerated {D B : FiniteHidden.{u,v} L₀}
    (S : RootScheme L₀) (commutes : E.SupportsCommute S)
    (b : ExpansionOn ρ.toReduct E.expandedAge B)
    (j : Structure.Embedding D.model B.model) (generated : RootGenerated D.model S) :
    ExpansionOn ρ.toReduct E.expandedAge D :=
  E.restrictOn b j (expanded_image_closed ρ S D.model b.model
    (j.targetCongr b.reduct_eq.symm) generated (commutes b.toHidden b.member))

def restrictGeneratedEmbedding {D B : FiniteHidden.{u,v} L₀}
    (S : RootScheme L₀) (commutes : E.SupportsCommute S)
    (b : ExpansionOn ρ.toReduct E.expandedAge B)
    (j : Structure.Embedding D.model B.model) (generated : RootGenerated D.model S) :
    Structure.Embedding (E.restrictGenerated S commutes b j generated).model b.model :=
  E.restrictOnEmbedding b j _

end ExpansionAges
end CCO.FullCode
