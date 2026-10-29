import CCO.HKNReservoir.LanguageNormalization
import AllThoseEPPA.TreeLikeInfiniteCopiesSurjectiveInverse
import AllThoseEPPA.TreeLikeInfiniteCopiesAmbientPostcompose
import AllThoseEPPA.TreeLikeHomEmbClosedIrreducibleImage
import Mathlib.Data.Set.Card

/-! One global normalization of an arbitrary distinguished HKN embedding.
The new carrier is literally the original source plus its complement; its
source inclusion has language 1 and vertex map Sum.inl, including empty
sources and empty-domain partial requests. -/
universe u v w
namespace CCO.HKNReservoir.DistinguishedNormalization
open AllThoseEPPA
noncomputable section
variable {L : Language.{u}} {Γ : Type w} [Group Γ] {act : L.Action Γ}
variable {α β δ : Type v} {A : Structure L α} {B : Structure L β} {D : Structure L δ}

private def autOfEmbedding (f : Structure.Embedding act D D)
    (hs : Function.Surjective f.toFun) : Structure.Automorphism act D where
  toPartialIsomorphism := {
    lang := f.lang
    toPartialEquiv := (Equiv.ofBijective f.toFun ⟨f.injective,hs⟩).toPartialEquiv
    source_closed := D.isClosed_univ
    target_closed := D.isClosed_univ
    map_rel_iff := fun R xs _ => f.map_rel_iff R xs
    map_func := fun F xs _ => f.map_func F xs }
  source_eq_univ := rfl
  target_eq_univ := rfl

theorem inverse_apply_image (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) (x : β) :
    e.inverseSurjective act he (e x) = x :=
  congrArg (fun f : Structure.Embedding act B B => f x)
    (Structure.Embedding.inverseSurjective_comp act e he)

theorem image_apply_inverse (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) (x : δ) :
    e (e.inverseSurjective act he x) = x :=
  congrArg (fun f : Structure.Embedding act D D => f x)
    (Structure.Embedding.comp_inverseSurjective act e he)

/-- Conjugation transports the actual language component as well as vertices. -/
def conjugateAut (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) (g : Structure.Automorphism act B) :
    Structure.Automorphism act D := by
  let inv := e.inverseSurjective act he
  have hi : Function.Surjective inv.toFun := fun x => ⟨e x,inverse_apply_image e he x⟩
  exact autOfEmbedding ((e.comp (g.toEmbedding act)).comp inv)
    (he.comp (g.toEquiv.surjective.comp hi))

@[simp] theorem conjugateAut_lang (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) (g : Structure.Automorphism act B) :
    (conjugateAut e he g).lang = e.lang * g.lang * e.lang⁻¹ := by
  change (e.lang * g.lang) * (e.inverseSurjective act he).lang = _
  rw [Structure.Embedding.inverseSurjective_lang]

@[simp] theorem conjugateAut_apply (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) (g : Structure.Automorphism act B) (x : δ) :
    conjugateAut e he g x = e (g (e.inverseSurjective act he x)) := rfl

@[simp] theorem conjugateAut_apply_image (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) (g : Structure.Automorphism act B) (x : β) :
    conjugateAut e he g (e x) = e (g x) := by
  rw [conjugateAut_apply,inverse_apply_image]

/-- EPPA transports along any genuine surjective Gamma-embedding. -/
theorem transportEPPA (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) (ψ : Structure.Embedding act A B)
    (h : Structure.IsEPPAWitness act ψ) :
    Structure.IsEPPAWitness act (e.comp ψ) := by
  intro p
  obtain ⟨g,hg⟩ := h p
  refine ⟨conjugateAut e he g,?_,?_⟩
  · change (conjugateAut e he g).lang * (e.lang * ψ.lang) = (e.lang * ψ.lang) * p.lang
    rw [conjugateAut_lang]
    simpa only [mul_assoc,inv_mul_cancel_left] using congrArg (fun k => e.lang * k) hg.1
  · intro x hx
    change conjugateAut e he g (e (ψ x)) = e (ψ (p x))
    rw [conjugateAut_apply_image,hg.2 x hx]

private theorem embeddingOn (e : Structure.Embedding act B D) (S : Set β) :
    Structure.Homomorphism.IsEmbeddingOn act e.toHomomorphism S :=
  ⟨fun _ _ _ _ h => e.injective h,fun R xs _ => e.map_rel_iff R xs,
    fun F xs _ => e.map_func F xs⟩

/-- Faithfulness transfers on EVERY closed irreducible subset. -/
theorem transportFaithful (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) (ψ : Structure.Embedding act A B)
    (h : Structure.IsIrreducibleStructureFaithful act ψ) :
    Structure.IsIrreducibleStructureFaithful act (e.comp ψ) := by
  intro S hS hIrr
  let inv := e.inverseSurjective act he
  let T : Set β := inv.toFun '' S
  have hT : B.IsClosed T :=
    Structure.Homomorphism.image_isClosed_of_embeddingOn act inv.toHomomorphism S hS (embeddingOn inv S)
  have hIrrT : (B.induce T hT).IsIrreducible :=
    Structure.Homomorphism.image_isIrreducible_of_embeddingOn act inv.toHomomorphism S hS (embeddingOn inv S) hIrr
  obtain ⟨g,hg⟩ := h T hT hIrrT
  refine ⟨conjugateAut e he g,?_⟩
  intro x hx
  obtain ⟨a,ha⟩ := hg (inv x) ⟨x,hx,rfl⟩
  refine ⟨a,?_⟩
  change e (g (inv x)) = e (ψ a)
  exact congrArg e.toFun ha

/-- Local HKN maps retain the single global presentation of the whole tree. -/
def LocalTrees (act : L.Action Γ) (A : Structure L α) (B : Structure L β) (n : ℕ) : Prop :=
  ∀ (S : Set β) (hS : B.IsClosed S), S.ncard ≤ n →
    ∃ (U : Type v) (T : Structure L U), Nonempty (TreePresentation act A T) ∧
      ∃ f : Structure.Homomorphism act (B.induce S hS) T,
        Structure.Homomorphism.IsHomomorphismEmbedding act f

/-- Cardinalities count all closed vertices, not packets. No injectivity
of the resulting local homomorphism is introduced by this transport. -/
theorem transportLocalTrees (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) {n : ℕ}
    (h : LocalTrees act A B n) : LocalTrees act A D n := by
  intro S hS hBound
  let inv := e.inverseSurjective act he
  let T : Set β := inv.toFun '' S
  have hT : B.IsClosed T :=
    Structure.Homomorphism.image_isClosed_of_embeddingOn act inv.toHomomorphism S hS (embeddingOn inv S)
  have hCard : T.ncard = S.ncard := Set.ncard_image_of_injective S inv.injective
  obtain ⟨U,C,hTree,f,hf⟩ := h T hT (hCard.trans_le hBound)
  let j : Structure.Embedding act (D.induce S hS) (B.induce T hT) :=
    Structure.Homomorphism.embeddingOnClosedImage act inv.toHomomorphism S hS (embeddingOn inv S)
  refine ⟨U,C,hTree,f.comp j.toHomomorphism,?_⟩
  exact Structure.Homomorphism.comp_isHomomorphismEmbedding act f j.toHomomorphism hf
    (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding act j)

/-- Retain the global map to the supplied first witness after normalization. -/
def transportBackmap (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) {C : Structure L α}
    (f : Structure.Homomorphism act B C) : Structure.Homomorphism act D C :=
  f.comp (e.inverseSurjective act he).toHomomorphism

@[simp] theorem transportBackmap_lang (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) {C : Structure L α}
    (f : Structure.Homomorphism act B C) :
    (transportBackmap e he f).lang = f.lang * e.lang⁻¹ := by
  change f.lang * (e.inverseSurjective act he).lang = _
  rw [Structure.Embedding.inverseSurjective_lang]

theorem transportBackmap_homomorphismEmbedding (e : Structure.Embedding act B D)
    (he : Function.Surjective e.toFun) {C : Structure L α}
    (f : Structure.Homomorphism act B C)
    (hf : Structure.Homomorphism.IsHomomorphismEmbedding act f) :
    Structure.Homomorphism.IsHomomorphismEmbedding act (transportBackmap e he f) :=
  Structure.Homomorphism.comp_isHomomorphismEmbedding act f
    (e.inverseSurjective act he).toHomomorphism hf
    (Structure.Homomorphism.Embedding.toHomomorphism_isHomomorphismEmbedding act
      (e.inverseSurjective act he))

/-- The complement is genuine unused vertices; no nonempty-source choice. -/
abbrev New (ψ : Structure.Embedding act A B) := {x : β // x ∉ Set.range ψ.toFun}

def literalEquiv (ψ : Structure.Embedding act A B) : (α ⊕ New ψ) ≃ β :=
  Equiv.ofBijective (Sum.elim ψ.toFun Subtype.val) (by
    constructor
    · intro x y h
      cases x with
      | inl x =>
        cases y with
        | inl y => exact congrArg Sum.inl (ψ.injective h)
        | inr y => exact (y.property ⟨x,h⟩).elim
      | inr x =>
        cases y with
        | inl y => exact (x.property ⟨y,h.symm⟩).elim
        | inr y => exact congrArg Sum.inr (Subtype.ext h)
    · intro x
      by_cases hx : x ∈ Set.range ψ.toFun
      · obtain ⟨a,rfl⟩ := hx
        exact ⟨Sum.inl a,rfl⟩
      · exact ⟨Sum.inr ⟨x,hx⟩,rfl⟩)

@[simp] theorem literalEquiv_inl (ψ : Structure.Embedding act A B) (x : α) :
    literalEquiv ψ (Sum.inl x) = ψ x := rfl

private def pullback (C : Structure L β) {U : Type v} (q : U ≃ β) : Structure L U where
  rel R xs := C.rel R (q ∘ xs)
  func F xs := {y | q y ∈ C.func F (q ∘ xs)}

private def rename (C : Structure L β) {U : Type v} (q : U ≃ β) :
    Structure.Embedding act C (pullback C q) where
  lang := 1
  toFun := q.symm
  injective := q.symm.injective
  map_rel_iff := by
    intro n R xs
    change C.rel (act.onRel 1 R) (q ∘ (q.symm ∘ xs)) ↔ C.rel R xs
    have he : q ∘ (q.symm ∘ xs) = xs := by funext i; exact q.apply_symm_apply (xs i)
    rw [Language.Action.onRel_one,he]
  map_func := by
    intro n F xs
    rw [Language.Action.onFunc_one]
    ext y
    change (∃ x ∈ C.func F xs, q.symm x = y) ↔ q y ∈ C.func F (q ∘ (q.symm ∘ xs))
    have he : q ∘ (q.symm ∘ xs) = xs := by funext i; exact q.apply_symm_apply (xs i)
    rw [he]
    constructor
    · rintro ⟨x,hx,rfl⟩
      simpa only [Equiv.apply_symm_apply] using hx
    · intro hy
      exact ⟨q y,hy,q.symm_apply_apply y⟩

/-- Relabel the WHOLE witness once, then rename vertices by one bijection. -/
def model (ψ : Structure.Embedding act A B) : Structure L (α ⊕ New ψ) :=
  pullback (B.relabel act ψ.lang⁻¹) (literalEquiv ψ)

def iso (ψ : Structure.Embedding act A B) : Structure.Embedding act B (model ψ) :=
  (rename (B.relabel act ψ.lang⁻¹) (literalEquiv ψ)).comp
    ((Structure.Embedding.id B).relabelTarget act ψ.lang⁻¹)

@[simp] theorem iso_lang (ψ : Structure.Embedding act A B) : (iso ψ).lang = ψ.lang⁻¹ := by
  change 1 * (ψ.lang⁻¹ * 1) = ψ.lang⁻¹
  simp

@[simp] theorem iso_apply (ψ : Structure.Embedding act A B) (x : β) :
    iso ψ x = (literalEquiv ψ).symm x := rfl

theorem iso_surjective (ψ : Structure.Embedding act A B) : Function.Surjective (iso ψ).toFun :=
  (literalEquiv ψ).symm.surjective

@[simp] theorem iso_apply_source (ψ : Structure.Embedding act A B) (x : α) :
    iso ψ (ψ x) = Sum.inl x := by
  change (literalEquiv ψ).symm (ψ x) = Sum.inl x
  apply (literalEquiv ψ).injective
  exact (literalEquiv ψ).apply_symm_apply (ψ x)

def inclusion (ψ : Structure.Embedding act A B) : Structure.Embedding act A (model ψ) where
  lang := 1
  toFun := Sum.inl
  injective := Sum.inl_injective
  map_rel_iff := by
    intro n R xs
    have h := ((iso ψ).comp ψ).map_rel_iff R xs
    have hl : ((iso ψ).comp ψ).lang = 1 := by change (iso ψ).lang * ψ.lang = 1; simp
    have hv : ((iso ψ).comp ψ).toFun = Sum.inl := funext (iso_apply_source ψ)
    simpa only [hl,hv] using h
  map_func := by
    intro n F xs
    have h := ((iso ψ).comp ψ).map_func F xs
    have hl : ((iso ψ).comp ψ).lang = 1 := by change (iso ψ).lang * ψ.lang = 1; simp
    have hv : ((iso ψ).comp ψ).toFun = Sum.inl := funext (iso_apply_source ψ)
    simpa only [hl,hv] using h

@[simp] theorem inclusion_lang (ψ : Structure.Embedding act A B) : (inclusion ψ).lang = 1 := rfl
@[simp] theorem inclusion_apply (ψ : Structure.Embedding act A B) (x : α) : inclusion ψ x = Sum.inl x := rfl

theorem iso_comp (ψ : Structure.Embedding act A B) : (iso ψ).comp ψ = inclusion ψ := by
  apply Structure.Embedding.ext_of_lang_toFun act
  · change (iso ψ).lang * ψ.lang = 1
    simp
  · exact funext (iso_apply_source ψ)

theorem normalizedEPPA (ψ : Structure.Embedding act A B)
    (h : Structure.IsEPPAWitness act ψ) : Structure.IsEPPAWitness act (inclusion ψ) := by
  rw [←iso_comp]
  exact transportEPPA (iso ψ) (iso_surjective ψ) ψ h

theorem normalizedFaithful (ψ : Structure.Embedding act A B)
    (h : Structure.IsIrreducibleStructureFaithful act ψ) :
    Structure.IsIrreducibleStructureFaithful act (inclusion ψ) := by
  rw [←iso_comp]
  exact transportFaithful (iso ψ) (iso_surjective ψ) ψ h

theorem normalizedLocalTrees (ψ : Structure.Embedding act A B) {n : ℕ}
    (h : LocalTrees act A B n) : LocalTrees act A (model ψ) n :=
  transportLocalTrees (iso ψ) (iso_surjective ψ) h

/-- All requested components, including empty-domain requests, extend with
the EXACT original gamma once the distinguished inclusion has language 1. -/
theorem normalized_extensions_exact (ψ : Structure.Embedding act A B)
    (h : Structure.IsEPPAWitness act ψ) (p : Structure.PartialAutomorphism act A) :
    ∃ g : Structure.Automorphism act (model ψ), g.lang = p.lang ∧
      ∀ x, x ∈ p.source → g (Sum.inl x) = Sum.inl (p x) := by
  obtain ⟨g,hg⟩ := normalizedEPPA ψ h p
  exact ⟨g,by simpa only [inclusion_lang,mul_one,one_mul] using hg.1,hg.2⟩

end
end CCO.HKNReservoir.DistinguishedNormalization
