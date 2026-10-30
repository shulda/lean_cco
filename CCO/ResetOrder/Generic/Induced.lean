import CCO.ResetOrder.Generic.FiniteAge

universe u v w
namespace CCO.ResetOrder.Generic.Structure
variable {S : Type u} {L : Language S} {V : Type v} {W : Type w}

/-- Literal inverse-image interpretations, before any closedness claim. -/
def pullback (C : Structure L W) (f : V → W) (hf : Function.Injective f) :
    Structure L V where
  sort x := C.sort (f x)
  func F xs := {y | f y ∈ C.func F (f ∘ xs)}
  functional F xs y z hy hz := hf (C.functional F (f ∘ xs) (f y) (f z) hy hz)
  func_sorted F xs y hy := C.func_sorted F (f ∘ xs) (f y) hy
  rel R xs := C.rel R (f ∘ xs)
  rel_sorted R xs hy := C.rel_sorted R (f ∘ xs) hy

/-- Closedness is precisely what prevents a pullback losing function domains. -/
def pullbackEmbedding (C : Structure L W) (f : V → W) (hf : Function.Injective f)
    (hclosed : C.Closed (Set.range f)) : Embedding (C.pullback f hf) C where
  point := f
  injective := hf
  sort_eq _ := rfl
  func_eq F xs := by
    apply Set.ext
    intro y
    constructor
    · intro hy
      obtain ⟨z, hz⟩ := hclosed F (f ∘ xs) (fun i => ⟨xs i, rfl⟩) hy
      refine ⟨z, ?_, hz⟩
      change f z ∈ C.func F (f ∘ xs)
      rw [hz]
      exact hy
    · rintro ⟨z, hz, rfl⟩
      exact hz
  rel_iff _ _ := Iff.rfl

theorem Embedding.closed_range {B : Structure L V} {C : Structure L W}
    (e : Embedding B C) : C.Closed (Set.range e.point) := by
  classical
  intro n F xs hx y hy
  let ys : Fin n → V := fun i => Classical.choose (hx i)
  have he : e.point ∘ ys = xs := funext (fun i => Classical.choose_spec (hx i))
  have hy' : y ∈ C.func F (e.point ∘ ys) := by rw [he]; exact hy
  obtain ⟨z, _, hz⟩ := e.reflect_func F ys y hy'
  exact ⟨z, hz⟩

/-- Ordinary closed restriction is the same construction along subtype inclusion. -/
def induce (C : Structure L V) (A : Set V) (_hA : C.Closed A) : Structure L A :=
  C.pullback Subtype.val Subtype.val_injective

def inclusion (C : Structure L V) (A : Set V) (hA : C.Closed A) :
    Embedding (C.induce A hA) C :=
  C.pullbackEmbedding Subtype.val Subtype.val_injective (by
    intro n F xs hx y hy
    have hxA : ∀ i, xs i ∈ A := by
      intro i
      obtain ⟨z, hz⟩ := hx i
      exact hz ▸ z.property
    exact ⟨⟨y, hA F xs hxA hy⟩, rfl⟩)

end CCO.ResetOrder.Generic.Structure
