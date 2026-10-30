import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.Data.Finite.Prod
import Mathlib.Data.Finite.Sigma

/-! Finite composition of unary expansion reducts. In actual applications
objects are complete finite named diagrams and morphisms are induced
embeddings. The lifting property retains the SAME prescribed old map;
precompactness is finiteness of expansions of one fixed old object. -/
universe u v w u₁ v₁ w₁
namespace CCO.APCharacter.Towers
open CategoryTheory
variable {C : Type u} {D : Type v} {E : Type w}
variable [Category.{u₁} C] [Category.{v₁} D] [Category.{w₁} E]

/-- An actual expansion exists for each old finite diagram. -/
def ReductSurjective (F : C ⥤ D) : Prop := Function.Surjective F.obj

/-- The exact old embedding is lifted, with only its target expansion
chosen. Equality of old target objects is retained explicitly. -/
def Reasonable (F : C ⥤ D) : Prop :=
  ∀ (A : C) (B : D) (f : F.obj A ⟶ B),
    ∃ (B' : C) (g : A ⟶ B'), F.obj B' = B ∧ HEq (F.map g) f

/-- Finitely many expansions on the fixed old object/carrier. -/
def Precompact (F : C ⥤ D) : Prop := ∀ B : D, Finite {A : C // F.obj A = B}

theorem reductSurjective_comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : ReductSurjective F) (hG : ReductSurjective G) :
    ReductSurjective (F ⋙ G) := hG.comp hF

theorem reasonable_comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : Reasonable F) (hG : Reasonable G) : Reasonable (F ⋙ G) := by
  intro A B f
  obtain ⟨Y,h,hY,hh⟩ := hG (F.obj A) B f
  obtain ⟨Z,k,hZ,hk⟩ := hF A Y h
  subst Y
  have hk' : F.map k = h := eq_of_heq hk
  refine ⟨Z,k,hY,?_⟩
  change HEq (G.map (F.map k)) f
  rw [hk']
  exact hh

/-- A composite fibre injects into the finite union of finite intermediate
fibres. No canonical target-expansion choice is assumed. -/
theorem precompact_comp {F : C ⥤ D} {G : D ⥤ E}
    (hF : Precompact F) (hG : Precompact G) : Precompact (F ⋙ G) := by
  intro B
  letI := hG B
  letI : ∀ Y : {A : D // G.obj A = B}, Finite {A : C // F.obj A = Y.val} :=
    fun Y => hF Y.val
  let target := Σ Y : {A : D // G.obj A = B}, {A : C // F.obj A = Y.val}
  let code : {A : C // (F ⋙ G).obj A = B} → target :=
    fun A => ⟨⟨F.obj A.val,A.property⟩,⟨A.val,rfl⟩⟩
  apply Finite.of_injective code
  intro A A' h
  apply Subtype.ext
  exact congrArg (fun x : target => x.2.val) h

/-- The identity reduct is the zero-stage expansion, including empty ages. -/
theorem identity_properties :
    ReductSurjective (𝟭 C) ∧ Reasonable (𝟭 C) ∧ Precompact (𝟭 C) := by
  refine ⟨Function.surjective_id,?_,?_⟩
  · intro A B f
    exact ⟨B,f,rfl,HEq.rfl⟩
  · intro B
    have h : Subsingleton {A : C // (𝟭 C).obj A = B} := by
      constructor
      intro A A'
      exact Subtype.ext (A.property.trans A'.property.symm)
    letI := h
    infer_instance

/-- A concrete finite-age category. The objects can be actual finite
named diagrams on finite ordinals; its morphisms are their embeddings. -/
structure UnaryAge where
  Obj : Type u
  category : Category.{u₁} Obj
attribute [instance] UnaryAge.category

/-- Data of one genuine finite unary expansion, including the literal
forgetful functor and the three proved expansion properties. -/
structure UnaryTransition (A B : UnaryAge.{u,u₁}) where
  forget : B.Obj ⥤ A.Obj
  reasonable : Reasonable forget
  reductSurjective : ReductSurjective forget
  precompact : Precompact forget

namespace UnaryTransition
variable {A B F : UnaryAge.{u,u₁}}

def identity (A : UnaryAge.{u,u₁}) : UnaryTransition A A where
  forget := 𝟭 A.Obj
  reasonable := identity_properties.2.1
  reductSurjective := identity_properties.1
  precompact := identity_properties.2.2

def compose (s : UnaryTransition A B) (t : UnaryTransition B F) : UnaryTransition A F where
  forget := t.forget ⋙ s.forget
  reasonable := reasonable_comp t.reasonable s.reasonable
  reductSurjective := reductSurjective_comp t.reductSurjective s.reductSurjective
  precompact := precompact_comp t.precompact s.precompact

end UnaryTransition

end CCO.APCharacter.Towers
