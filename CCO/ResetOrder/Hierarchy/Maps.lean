import CCO.ResetOrder.Hierarchy.Normalize

/-! Normalized embedding preservation follows by induction on the actual
coarse-first rank; reflection follows from totality and injectivity. -/
universe u v w
namespace CCO.ResetOrder.Hierarchy
namespace System
variable {I : Type u} {H : Schedule I} {X : I → Type v} {Y : I → Type w}
variable {S : System H X} {T : System H Y}
structure Map (S : System H X) (T : System H Y) where
  point : ∀ i, X i → Y i
  injective : ∀ i, Function.Injective (point i)
  up_commute : ∀ i a x, T.up i a (point i x) = point (H.coordinate i a) (S.up i a x)

namespace Map
variable (f : Map S T)
theorem parent_iff (i : I) (x y : X i) :
    T.parent i (f.point i x) (f.point i y) ↔ S.parent i x y := by
  rw [← T.key_parent, ← S.key_parent]
  simp only [f.up_commute, (f.injective _).eq_iff]

theorem normalize_preserves (t : S.Tasks) (s : T.Tasks)
    (ht : ∀ i x y, (t i).lt x y → (s i).lt (f.point i x) (f.point i y)) :
    ∀ i x y, (S.normalizeTasks t i).lt x y →
      (T.normalizeTasks s i).lt (f.point i x) (f.point i y) := by
  intro i
  induction i using (measure H.rank).wf.induction with
  | h i ih =>
    intro x y hxy
    rw [S.normalize_lt_iff] at hxy
    rw [T.normalize_lt_iff]
    rcases hxy with ⟨a, hbefore, hlt⟩ | ⟨hp, hlt⟩
    · left
      refine ⟨a, ?_, ?_⟩
      · intro b hb
        change T.up i b (f.point i x) = T.up i b (f.point i y)
        rw [f.up_commute, f.up_commute]
        exact congrArg (f.point (H.coordinate i b)) (hbefore b hb)
      · change (T.normalizeTasks s (H.coordinate i a)).lt
          (T.up i a (f.point i x)) (T.up i a (f.point i y))
        rw [f.up_commute, f.up_commute]
        exact ih (H.coordinate i a) (H.coordinate_rank i a) _ _ hlt
    · exact Or.inr ⟨(f.parent_iff i x y).2 hp, ht i x y hlt⟩

theorem normalize_reflects (t : S.Tasks) (s : T.Tasks)
    (ht : ∀ i x y, (t i).lt x y → (s i).lt (f.point i x) (f.point i y))
    (i : I) (x y : X i) :
    (T.normalizeTasks s i).lt (f.point i x) (f.point i y) ↔ (S.normalizeTasks t i).lt x y := by
  constructor
  · intro h
    by_cases he : x = y
    · subst y
      exact False.elim ((T.normalizeTasks s i).irrefl _ h)
    · rcases (S.normalizeTasks t i).total he with hxy | hyx
      · exact hxy
      · exact False.elim ((T.normalizeTasks s i).asymm h (f.normalize_preserves t s ht i y x hyx))
  · exact f.normalize_preserves t s ht i x y

def identity (S : System H X) : Map S S where
  point _ := id
  injective _ := Function.injective_id
  up_commute _ _ _ := rfl

def compose {Z : I → Type*} {U : System H Z} (g : Map T U) : Map S U where
  point i := g.point i ∘ f.point i
  injective i := (g.injective i).comp (f.injective i)
  up_commute i a x := by
    change U.up i a (g.point i (f.point i x)) = _
    rw [g.up_commute, f.up_commute]
    rfl
end Map
end System
end CCO.ResetOrder.Hierarchy
