import CCO.ResetOrder.Generic.Language

universe u v w z
namespace CCO.ResetOrder.Generic.Structure
variable {S : Type u} {L : Language S}
variable {V : Type v} {W : Type w} {X : Type z}

namespace Embedding
variable {A : Structure L V} {B : Structure L W} {C : Structure L X}

@[ext] theorem ext {f g : Embedding A B} (h : f.point = g.point) : f = g := by
  cases f
  cases g
  cases h
  rfl

def cast {A' : Structure L V} {B' : Structure L W}
    (f : Embedding A B) (hA : A = A') (hB : B = B') : Embedding A' B' := by
  subst A'
  subst B'
  exact f

@[simp] theorem point_cast {A' : Structure L V} {B' : Structure L W}
    (f : Embedding A B) (hA : A = A') (hB : B = B') :
    (f.cast hA hB).point = f.point := by
  subst A'
  subst B'
  rfl

def identity (A : Structure L V) : Embedding A A where
  point := id
  injective := Function.injective_id
  sort_eq _ := rfl
  func_eq _ _ := by simp only [Function.id_comp, Set.image_id]
  rel_iff _ _ := Iff.rfl

def compose (g : Embedding B C) (f : Embedding A B) : Embedding A C where
  point := g.point ∘ f.point
  injective := g.injective.comp f.injective
  sort_eq x := (g.sort_eq (f.point x)).trans (f.sort_eq x)
  func_eq F xs := by
    change C.func F (g.point ∘ (f.point ∘ xs)) = _
    rw [g.func_eq, f.func_eq, Set.image_image]
    rfl
  rel_iff R xs := (g.rel_iff R (f.point ∘ xs)).trans (f.rel_iff R xs)

theorem map_func (f : Embedding A B) {n} (F : L.Func n) xs y
    (h : y ∈ A.func F xs) : f.point y ∈ B.func F (f.point ∘ xs) := by
  rw [f.func_eq]
  exact ⟨y, h, rfl⟩

theorem reflect_func (f : Embedding A B) {n} (F : L.Func n) xs y
    (h : y ∈ B.func F (f.point ∘ xs)) :
    ∃ z, z ∈ A.func F xs ∧ f.point z = y := by
  rw [f.func_eq] at h
  exact h

theorem domain_iff (f : Embedding A B) {n} (F : L.Func n) xs :
    (B.func F (f.point ∘ xs)).Nonempty ↔ (A.func F xs).Nonempty := by
  rw [f.func_eq, Set.image_nonempty]

/-- Two induced source structures on the SAME carrier and SAME vertex map agree.
This proves the structural uniqueness used by normalization; it is not a gate. -/
theorem same_map_domain_unique {D : Structure L V}
    (f : Embedding A B) (g : Embedding D B) (h : f.point = g.point) : A = D := by
  apply Structure.ext
  · funext x
    exact (f.sort_eq x).symm.trans (h ▸ g.sort_eq x)
  · funext n F xs
    apply Set.ext
    intro y
    constructor
    · intro hy
      have hf := f.map_func F xs y hy
      rw [h] at hf
      obtain ⟨z, hz, he⟩ := g.reflect_func F xs (g.point y) hf
      exact g.injective he ▸ hz
    · intro hy
      have hg := g.map_func F xs y hy
      rw [← h] at hg
      obtain ⟨z, hz, he⟩ := f.reflect_func F xs (f.point y) hg
      exact f.injective he ▸ hz
  · funext n R xs
    apply propext
    rw [← f.rel_iff R xs, ← g.rel_iff R xs, h]

end Embedding
end CCO.ResetOrder.Generic.Structure
