import CCO.ResetOrder.Generic.Embedding

universe u v
namespace CCO.ResetOrder.Generic
variable {S : Type u} (L : Language S)

/-- Keeping the actual carrier makes restrictions and competitors literal. -/
structure Object where
  Carrier : Type v
  finite : Finite Carrier
  data : Structure L Carrier

attribute [instance] Object.finite
abbrev Age := Object.{u,v} L → Prop

namespace Object
variable {L}
abbrev Embedding (A B : Object.{u,v} L) := A.data.Embedding B.data

def withData (A : Object.{u,v} L) (d : Structure L A.Carrier) : Object.{u,v} L :=
  ⟨A.Carrier, A.finite, d⟩

def identity (A : Object.{u,v} L) : Embedding A A := .identity A.data

def compose {A B C : Object.{u,v} L} (g : Embedding B C) (f : Embedding A B) :
    Embedding A C := g.compose f

end Object

/-- Heredity under all induced embeddings includes isomorphism closure. -/
def Hereditary (K : Age.{u,v} L) : Prop :=
  ∀ {A B}, K B → Object.Embedding A B → K A

def JointEmbedding (K : Age.{u,v} L) : Prop :=
  ∀ A B, K A → K B → ∃ C, K C ∧
    Nonempty (Object.Embedding A C) ∧ Nonempty (Object.Embedding B C)

/-- All embeddings are coloured, with an arbitrary positive finite number of colours. -/
def Arrow (A B C : Object.{u,v} L) (k : ℕ) : Prop :=
  ∀ χ : Object.Embedding A C → Fin (k + 1),
    ∃ (g : Object.Embedding B C) (c : Fin (k + 1)),
      ∀ f : Object.Embedding A B, χ (g.compose f) = c

def Ramsey (K : Age.{u,v} L) : Prop :=
  ∀ A B, K A → K B → ∀ k, ∃ C, K C ∧ Arrow L A B C k

end CCO.ResetOrder.Generic
