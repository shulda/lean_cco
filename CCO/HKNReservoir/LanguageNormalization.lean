import CCO.HKNReservoir.MorphismBridge
import AllThoseEPPA.TreeLikeFullAAmalgamation
import AllThoseEPPA.TreeLikeAmalgamRelabel
import AllThoseEPPA.Irreducible

universe u v w
namespace CCO.HKNReservoir
open AllThoseEPPA
variable {L : Language.{u}} {Γ : Type w} [Group Γ] (act : L.Action Γ)
variable {V W : Type v}

/-- A literal upstream tree plus one global, surjective language view.
Every node and every overlap is seen through the SAME view component. -/
structure TreePresentation (A : Structure L V) (D : Structure L W) where
  Core : Type v
  core : Structure L Core
  tree : TreeLike.TreeAmalgamation act A core
  view : Structure.Embedding act core D
  view_surjective : Function.Surjective view.toFun

namespace TreePresentation
variable {act} {A : Structure L V} {D : Structure L W}

def ofTree (h : TreeLike.TreeAmalgamation act A D) : TreePresentation act A D where
  Core := W
  core := D
  tree := h
  view := Structure.Embedding.id D
  view_surjective x := ⟨x,rfl⟩

/-- ONE global relabel updates the view of the ENTIRE tree. -/
def relabelTarget (P : TreePresentation act A D) (κ : Γ) : TreePresentation act A (D.relabel act κ) where
  Core := P.Core
  core := P.core
  tree := P.tree
  view := P.view.relabelTarget act κ
  view_surjective := P.view_surjective

@[simp] theorem relabelTarget_view_lang (P : TreePresentation act A D) (κ : Γ) :
    (P.relabelTarget κ).view.lang = κ * P.view.lang := rfl
@[simp] theorem relabelTarget_view_apply (P : TreePresentation act A D) (κ : Γ) (x : P.Core) :
    (P.relabelTarget κ).view x = P.view x := rfl
end TreePresentation

namespace Homomorphism
variable {act} {A : Structure L V} {D : Structure L W}

def relabelTarget (f : Structure.Homomorphism act A D) (κ : Γ) :
    Structure.Homomorphism act A (D.relabel act κ) where
  lang := κ*f.lang
  toFun := f.toFun
  map_rel := by
    intro n R xs hx
    change D.rel (act.onRel κ⁻¹ (act.onRel (κ*f.lang) R)) (f.toFun ∘ xs)
    rw [←act.onRel_mul,inv_mul_cancel_left]
    exact f.map_rel R xs hx
  map_func := by
    intro n F xs
    change Structure.imageSet f.toFun (A.func F xs) ⊆ D.func (act.onFunc κ⁻¹ (act.onFunc (κ*f.lang) F)) (f.toFun ∘ xs)
    rw [←act.onFunc_mul,inv_mul_cancel_left]
    exact f.map_func F xs

theorem relabelTarget_embeddingOn (f : Structure.Homomorphism act A D) (κ : Γ)
    (S : Set V) (h : Structure.Homomorphism.IsEmbeddingOn act f S) :
    Structure.Homomorphism.IsEmbeddingOn act (relabelTarget f κ) S := by
  refine ⟨h.1,?_,?_⟩
  · intro n R xs hxs
    change D.rel (act.onRel κ⁻¹ (act.onRel (κ*f.lang) R)) (f.toFun ∘ xs) ↔ A.rel R xs
    rw [←act.onRel_mul,inv_mul_cancel_left]
    exact h.2.1 R xs hxs
  · intro n F xs hxs
    change Structure.imageSet f.toFun (A.func F xs) = D.func (act.onFunc κ⁻¹ (act.onFunc (κ*f.lang) F)) (f.toFun ∘ xs)
    rw [←act.onFunc_mul,inv_mul_cancel_left]
    exact h.2.2 F xs hxs

theorem relabelTarget_homomorphismEmbedding (f : Structure.Homomorphism act A D) (κ : Γ)
    (h : Structure.Homomorphism.IsHomomorphismEmbedding act f) :
    Structure.Homomorphism.IsHomomorphismEmbedding act (relabelTarget f κ) :=
  fun S hS hi => relabelTarget_embeddingOn f κ S (h S hS hi)

def normalize (f : Structure.Homomorphism act A D) :
    Structure.Homomorphism act A (D.relabel act f.lang⁻¹) := relabelTarget f f.lang⁻¹

@[simp] theorem normalize_lang (f : Structure.Homomorphism act A D) : (normalize f).lang = 1 := inv_mul_cancel f.lang
@[simp] theorem normalize_apply (f : Structure.Homomorphism act A D) (x : V) : normalize f x = f x := rfl

theorem normalize_homomorphismEmbedding (f : Structure.Homomorphism act A D)
    (h : Structure.Homomorphism.IsHomomorphismEmbedding act f) :
    Structure.Homomorphism.IsHomomorphismEmbedding act (normalize f) := relabelTarget_homomorphismEmbedding f f.lang⁻¹ h
end Homomorphism

/-- C12: the single normalized map and the globally normalized WHOLE
presentation retain all irreducible embedding restrictions. -/
theorem normalize_local_tree {A : Structure L V} {P : Structure L V} {D : Structure L W}
    (T : TreePresentation act A D) (f : Structure.Homomorphism act P D)
    (hf : Structure.Homomorphism.IsHomomorphismEmbedding act f) :
    Nonempty (TreePresentation act A (D.relabel act f.lang⁻¹)) ∧
      (Homomorphism.normalize f).lang = 1 ∧
      Structure.Homomorphism.IsHomomorphismEmbedding act (Homomorphism.normalize f) :=
  ⟨⟨T.relabelTarget f.lang⁻¹⟩,Homomorphism.normalize_lang f,Homomorphism.normalize_homomorphismEmbedding f hf⟩

end CCO.HKNReservoir
