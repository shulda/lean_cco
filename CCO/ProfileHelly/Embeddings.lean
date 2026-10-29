import CCO.ProfileHelly.SemanticCycles

universe u v z y w
namespace CCO.ProfileHelly.Network
variable {ι : Type u} {T : Table.{u,v} ι}
variable {V : Type z} {W : Type y} {X : Type w}
variable {sort : V → ι} {targetSort : W → ι} {thirdSort : X → ι}

/-- Full induced typed embeddings preserve ALL literal pair colours,
including the diagonal; they are not merely homomorphisms of partial records. -/
structure Embedding (D : Network T sort) (E : Network T targetSort) where
  point : V → W
  injective : Function.Injective point
  preserves : ∀ x y, E.tagged (point x) (point y) = D.tagged x y

namespace Embedding
variable {D : Network T sort} {E : Network T targetSort} {F : Network T thirdSort}

theorem sort_eq (f : Embedding D E) (x : V) : targetSort (f.point x) = sort x :=
  congrArg Sigma.fst (f.preserves x x)

def toHom (f : Embedding D E) : D.Hom E where
  point := f.point
  sort_eq := f.sort_eq
  preserves := by
    intro x y a ha
    rw [f.preserves]
    exact congrArg (fun c => (⟨sort x,sort y,c⟩ : Σ i,Σ j,Option (T.Atom i j))) ha

def id (D : Network T sort) : Embedding D D where
  point := _root_.id
  injective := Function.injective_id
  preserves := fun _ _ => rfl

def comp (g : Embedding E F) (f : Embedding D E) : Embedding D F where
  point := g.point ∘ f.point
  injective := g.injective.comp f.injective
  preserves := fun x y => (g.preserves (f.point x) (f.point y)).trans (f.preserves x y)
end Embedding

def Hom.ofExtends (D E : Network T sort) (h : D.Extends E) : D.Hom E where
  point := _root_.id
  sort_eq := fun _ => rfl
  preserves := by
    intro x y a ha
    exact congrArg (fun c => (⟨sort x,sort y,c⟩ : Σ i,Σ j,Option (T.Atom i j))) (h x y a ha)

end CCO.ProfileHelly.Network
