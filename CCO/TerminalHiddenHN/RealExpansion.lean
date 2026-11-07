import CCO.Finite
import Mathlib.Basic.Finite.Prod
import Mathlib.Data.Fintype.Pi

/-! Concrete finite relational expansions of the ORIGINAL real age.
Objects keep their entire old induced structure. Only finitely many
unary/binary predicates are added; their interpretations determine an
expansion uniquely. Restriction is along every old induced embedding.
Ramsey colours ALL actual expanded embeddings, and reasonableness lifts
the SAME old embedding. There is no expansion-property assertion. -/

universe u v w l k
namespace CCO.TerminalHiddenHN

variable {ι : Type u} {X : ι → Type v}

structure RealExpansionData (S : AtomicSource.{u,v,w} ι X) where
  Unary : Type l
  Binary : Type l
  finiteUnary : Finite Unary
  finiteBinary : Finite Binary
  unarySort : Unary → ι
  leftSort : Binary → ι
  rightSort : Binary → ι
  Expansion : FiniteInduced (X := X) → Type k
  nonempty : ∀ A, Nonempty (Expansion A)
  unary : {A : FiniteInduced (X := X)} → Expansion A → Unary → A.vertices → Prop
  binary : {A : FiniteInduced (X := X)} → Expansion A → Binary → A.vertices → A.vertices → Prop
  unary_sorted : ∀ {A} (a : Expansion A) R x, unary a R x → x.val.1 = unarySort R
  binary_sorted : ∀ {A} (a : Expansion A) R x y, binary a R x y →
    x.val.1 = leftSort R ∧ y.val.1 = rightSort R
  faithful : ∀ {A} (a b : Expansion A),
    (∀ R x, unary a R x ↔ unary b R x) →
    (∀ R x y, binary a R x y ↔ binary b R x y) → a = b
  restrict : ∀ {A B}, InducedEmbedding S A B → Expansion B → Expansion A
  restrict_unary : ∀ {A B} (f : InducedEmbedding S A B) (b : Expansion B) R x,
    unary (restrict f b) R x ↔ unary b R (f.toEmbedding x)
  restrict_binary : ∀ {A B} (f : InducedEmbedding S A B) (b : Expansion B) R x y,
    binary (restrict f b) R x y ↔ binary b R (f.toEmbedding x) (f.toEmbedding y)

namespace RealExpansionData
variable {S : AtomicSource.{u,v,w} ι X} (E : RealExpansionData.{u,v,w,l,k} S)

/-- Precompactness is literal: the fixed old carrier has only finitely
many possible finite-language predicate tables, and they determine it. -/
theorem finite_expansions (A : FiniteInduced (X := X)) : Finite (E.Expansion A) := by
  classical
  letI : Finite E.Unary := E.finiteUnary
  letI : Finite E.Binary := E.finiteBinary
  letI : Finite A.vertices := A.finite_vertices.to_subtype
  let code (a : E.Expansion A) :
      (E.Unary → A.vertices → Prop) × (E.Binary → A.vertices → A.vertices → Prop) :=
    ⟨E.unary a,E.binary a⟩
  have hinj : Function.Injective code := by
    intro a b h
    have hu : E.unary a = E.unary b := congrArg Prod.fst h
    have hb : E.binary a = E.binary b := congrArg Prod.snd h
    apply E.faithful a b
    · intro R x
      exact Iff.of_eq (congrFun (congrFun hu R) x)
    · intro R x y
      exact Iff.of_eq (congrFun (congrFun (congrFun hb R) x) y)
  exact Finite.of_injective code hinj

structure Embedding {A B : FiniteInduced (X := X)}
    (a : E.Expansion A) (b : E.Expansion B) where
  old : InducedEmbedding S A B
  unary_iff : ∀ R x, E.unary b R (old.toEmbedding x) ↔ E.unary a R x
  binary_iff : ∀ R x y,
    E.binary b R (old.toEmbedding x) (old.toEmbedding y) ↔ E.binary a R x y

namespace Embedding
variable {E} {A B C : FiniteInduced (X := X)}
variable {a : E.Expansion A} {b : E.Expansion B} {c : E.Expansion C}

def comp (g : E.Embedding b c) (f : E.Embedding a b) : E.Embedding a c where
  old := {
    toEmbedding := f.old.toEmbedding.trans g.old.toEmbedding
    preserves_sort := fun x => (g.old.preserves_sort _).trans (f.old.preserves_sort x)
    preserves_colours := fun x y => (f.old.preserves_colours x y).trans
      (g.old.preserves_colours (f.old.toEmbedding x) (f.old.toEmbedding y)) }
  unary_iff R x := (g.unary_iff R _).trans (f.unary_iff R x)
  binary_iff R x y := (g.binary_iff R _ _).trans (f.binary_iff R x y)

@[ext] theorem ext {f g : E.Embedding a b}
    (h : ∀ x, f.old.toEmbedding x = g.old.toEmbedding x) : f = g := by
  cases f with
  | mk f fu fb =>
    cases g with
    | mk g gu gb =>
      have he : f = g := by
        cases f
        cases g
        have hp := Function.Embedding.ext h
        cases hp
        rfl
      cases he
      rfl

end Embedding

/-- Every induced restriction is an allowed object, with its literal
old inclusion/map and all unary/binary predicates reflected. -/
def restrictionEmbedding {A B : FiniteInduced (X := X)}
    (f : InducedEmbedding S A B) (b : E.Expansion B) : E.Embedding (E.restrict f b) b where
  old := f
  unary_iff R x := (E.restrict_unary f b R x).symm
  binary_iff R x y := (E.restrict_binary f b R x y).symm

def Reasonable : Prop :=
  ∀ (A B : FiniteInduced (X := X)) (f : InducedEmbedding S A B) (a : E.Expansion A),
    ∃ b : E.Expansion B, E.restrict f b = a

theorem reasonable_lift (h : E.Reasonable)
    {A B : FiniteInduced (X := X)} (f : InducedEmbedding S A B) (a : E.Expansion A) :
    ∃ (b : E.Expansion B) (g : E.Embedding a b), g.old = f := by
  obtain ⟨b,hb⟩ := h A B f a
  subst a
  exact ⟨b,E.restrictionEmbedding f b,rfl⟩

/-- The host and its allowed expansion are chosen BEFORE colouring all
expanded induced embeddings. Empty source-embedding sets are permitted. -/
def Ramsey : Prop :=
  ∀ (A B : FiniteInduced (X := X)) (a : E.Expansion A) (b : E.Expansion B)
    (n : ℕ), 0 < n →
    ∃ (C : FiniteInduced (X := X)) (c : E.Expansion C),
      ∀ colour : E.Embedding a c → Fin n,
        ∃ g : E.Embedding b c,
          ∀ f₁ f₂ : E.Embedding a b, colour (g.comp f₁) = colour (g.comp f₂)

end RealExpansionData

/-- A faithful finite unary/binary expansion of the actual original age,
hereditary by literal restriction, precompact by finite predicate tables,
reasonable along the same old embeddings, and Ramsey on ALL embeddings. -/
def HasFiniteRelationalRamseyExpansion (S : AtomicSource.{u,v,w} ι X) : Prop :=
  ∃ E : RealExpansionData.{u,v,w,l,k} S, E.Reasonable ∧ E.Ramsey

end CCO.TerminalHiddenHN
