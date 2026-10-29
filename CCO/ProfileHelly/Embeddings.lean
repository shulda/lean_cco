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

theorem Extends.tagged_some {D E : Network T sort} (h : D.Extends E)
    (x y : V) {i j : ι} (a : T.Atom i j)
    (he : D.tagged x y = ⟨i,j,some a⟩) : E.tagged x y = ⟨i,j,some a⟩ := by
  cases hc : D.edge x y with
  | none =>
    have hh := congrArg (fun c : Σ i,Σ j,Option (T.Atom i j) => c.2.2.isSome) he
    change (D.edge x y).isSome = true at hh
    rw [hc] at hh
    cases hh
  | some b =>
    have ht : E.tagged x y = D.tagged x y := by
      simp only [tagged,h x y b hc,hc]
    exact ht.trans he

/-- Completing a partial target preserves the ENTIRE induced embedding
of every complete factor. No absent cross-pair is asserted on that factor. -/
def Embedding.extend {D E : Network T targetSort}
    (C : CompleteNetwork T sort) (f : Embedding C.toNetwork D) (h : D.Extends E) :
    Embedding C.toNetwork E where
  point := f.point
  injective := f.injective
  preserves := by
    intro x y
    by_cases hxy : x = y
    · subst y
      have hd : E.tagged (f.point x) (f.point x) = D.tagged (f.point x) (f.point x) := by
        simp only [tagged,E.diagonal,D.diagonal]
      exact hd.trans (f.preserves x x)
    · obtain ⟨a,ha⟩ := C.complete x y hxy
      have htag : D.tagged (f.point x) (f.point y) = ⟨sort x,sort y,some a⟩ :=
        f.toHom.preserves x y a ha
      exact (h.tagged_some _ _ a htag).trans
        (congrArg (fun c => (⟨sort x,sort y,c⟩ : Σ i,Σ j,Option (T.Atom i j))) ha).symm

end CCO.ProfileHelly.Network
