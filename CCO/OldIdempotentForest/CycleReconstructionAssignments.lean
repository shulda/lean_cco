import CCO.Atomic

/-! Extend actual typed values on an injective finite OLD occurrence map.
The extension reads those SAME values; no new value is chosen on an old
occurrence in the image. Points outside the cycle are unused defaults. -/

universe u v w p q
namespace CCO.OldIdempotentForest

variable {ι : Type u} {X : ι → Type v} (S : AtomicSource.{u,v,w} ι X)
variable {A : Type p} {P : Type q} (sort : P → ι) (root : A ↪ P)
variable (point : ∀ a, X (sort (root a)))

private theorem rootPoint_transport (a b : A) (hab : a = b) (hr : root a = root b) :
    Eq.mp (congrArg (fun r => X (sort r)) hr) (point a) = point b := by
  cases hab
  rfl

noncomputable def extendTypedRootPoints (p : P) : X (sort p) := by
  classical
  by_cases h : ∃ a, root a = p
  · exact Eq.mp (congrArg (fun r => X (sort r)) h.choose_spec) (point h.choose)
  · exact Classical.choice (S.nonemptySort _)

theorem extendTypedRootPoints_at (a : A) :
    extendTypedRootPoints S sort root point (root a) = point a := by
  classical
  unfold extendTypedRootPoints
  have h : ∃ b, root b = root a := ⟨a,rfl⟩
  rw [dite_eq_left h]
  have he : h.choose = a := root.injective h.choose_spec
  exact rootPoint_transport sort root point _ _ he h.choose_spec

end CCO.OldIdempotentForest
