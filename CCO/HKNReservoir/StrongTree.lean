import CCO.HKNReservoir.TreeSupport
import AllThoseEPPA.StrongCompletionTreeAmalgamationClass

/-! Closed strong amalgamation preserves a genuinely injective realization
of an actual recursive tree, in addition to exactness on every closed
irreducible piece. The entire previous completed image is retained. -/
universe u v w
namespace CCO.HKNReservoir
open AllThoseEPPA
variable {L : Language.{u}} {Γ : Type w} [Group Γ]

structure FiniteStrongAmalgamationClass (act : L.Action Γ) where
  mem : {V : Type v} → Structure L V → Prop
  amalgamate : ∀ {I X Y : Type v}
    {C : Structure L I} {B₁ : Structure L X} {B₂ : Structure L Y}
    (f : Structure.Embedding act C B₁) (g : Structure.Embedding act C B₂),
    mem B₁ → mem B₂ →
    ∃ (Z : Type v) (_ : Finite Z) (D : Structure L Z), mem D ∧
      ∃ (l : Structure.Embedding act B₁ D) (r : Structure.Embedding act B₂ D),
        l.comp f = r.comp g ∧
        ∀ x y, l x = r y ↔ ∃ c, f c = x ∧ g c = y

/-- C07: a strong finite amalgamation class produces a globally injective
homomorphism-embedding of every literal full-source tree. -/
theorem tree_realization_in_strong_class
    (act : L.Action Γ) {U : Type v} (A : Structure L U) [Finite U]
    (hA : A.IsIrreducible) (K : FiniteStrongAmalgamationClass.{u,v,w} act)
    (hKA : K.mem A) {V : Type v} {D : Structure L V}
    (hTree : TreeLike.TreeAmalgamation act A D) :
    ∃ (Z : Type v) (_ : Finite Z) (E : Structure L Z), K.mem E ∧
      ∃ f : Structure.Homomorphism act D E,
        Function.Injective f.toFun ∧
        Structure.Homomorphism.IsHomomorphismEmbedding act f := by
  classical
  induction hTree with
  | copy C e hSurj =>
    let f := e.inverseSurjective act hSurj
    exact ⟨U,inferInstance,A,hKA,f.toHomomorphism,f.injective,
      Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding act f⟩
  | glue C B₁ B₂ hT₁ hT₂ δ₁ δ₂ α₁ α₂ ih₁ ih₂ =>
    obtain ⟨Z₁,hZ₁,E₁,hE₁,f₁,hinj₁,hf₁⟩ := ih₁
    obtain ⟨Z₂,hZ₂,E₂,hE₂,f₂,hinj₂,hf₂⟩ := ih₂
    let q₁ := (Structure.Homomorphism.compEmbedding_of_irreducible act f₁ hf₁ α₁ hA).comp δ₁
    let q₂ := (Structure.Homomorphism.compEmbedding_of_irreducible act f₂ hf₂ α₂ hA).comp δ₂
    obtain ⟨Z,hZ,E,hE,j₁,j₂,hbase,hcross⟩ := K.amalgamate q₁ q₂ hE₁ hE₂
    let t₁ := j₁.toHomomorphism.comp f₁
    let t₂ := j₂.toHomomorphism.comp f₂
    have ht₁ : Structure.Homomorphism.IsHomomorphismEmbedding act t₁ :=
      Structure.Homomorphism.comp_isHomomorphismEmbedding act _ _
        (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding act j₁) hf₁
    have ht₂ : Structure.Homomorphism.IsHomomorphismEmbedding act t₂ :=
      Structure.Homomorphism.comp_isHomomorphismEmbedding act _ _
        (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding act j₂) hf₂
    have hLang : t₁.lang * (α₁.comp δ₁).lang = t₂.lang * (α₂.comp δ₂).lang := by
      have hh := congrArg (fun z : Structure.Embedding act C E => z.lang) hbase
      change j₁.lang * ((f₁.lang * α₁.lang) * δ₁.lang) =
        j₂.lang * ((f₂.lang * α₂.lang) * δ₂.lang) at hh
      simpa only [t₁,t₂,Structure.Embedding.comp,Structure.Homomorphism.comp,
        Structure.Embedding.toHomomorphism,mul_assoc] using hh
    have hAgree : ∀ c, t₁ ((α₁.comp δ₁) c) = t₂ ((α₂.comp δ₂) c) := by
      intro c
      exact congrArg (fun z : Structure.Embedding act C E => z c) hbase
    let t := TreeLike.generalAmalgamGluedHomomorphism act
      (α₁.comp δ₁) (α₂.comp δ₂) t₁ t₂ hLang hAgree
    have ht : Structure.Homomorphism.IsHomomorphismEmbedding act t :=
      TreeLike.generalAmalgamGluedHomomorphism_isHomomorphismEmbedding act
        (α₁.comp δ₁) (α₂.comp δ₂) t₁ t₂ hLang hAgree ht₁ ht₂
    have hinj : Function.Injective t.toFun := by
      apply gluedCarrierMap_injective (α₁.comp δ₁).toFun (α₂.comp δ₂).toFun
        t₁.toFun t₂.toFun
        (j₁.injective.comp hinj₁) (j₂.injective.comp hinj₂)
      intro x y he
      obtain ⟨c,hc₁,hc₂⟩ := (hcross (f₁ x) (f₂ y)).mp he
      exact ⟨c,hinj₁ hc₁,hinj₂ hc₂⟩
    exact ⟨Z,hZ,E,hE,t,hinj,ht⟩

end CCO.HKNReservoir
