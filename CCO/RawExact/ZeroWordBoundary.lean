import CCO.RawExact.PathSkeleton

/-!
# B002 C06/C12: zero-length RAW words are real logical identity

Erasing identity letters can leave a path with ZERO diversity edges.
Such a word can only have matching source/target original sorts,
and its represented relation is the actual tagged diagonal.
It must be handled before the private-path graph construction:
there is no legitimate specified diversity edge from the root
to a distinct old centre for a zero-length word.

A positive word may still have DIAGONAL OUTPUTS; this theorem
deliberately says nothing about such words.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem zeroLength_sameSort {i j : ι} (word : RawWord S i j)
    (hZero : diversityLength S word = 0) : i = j := by
  induction word with
  | nil _ => rfl
  | identity tail ih => exact ih hZero
  | atom a tail ih =>
      simp [diversityLength] at hZero

/-- Exact identity-bearing evaluation, with both literal sort tags. -/
theorem zeroLength_relation_iff_tagged_eq {i j : ι}
    (word : RawWord S i j) :
    diversityLength S word = 0 →
      ∀ (x : X i) (y : X j),
        RawWord.relation S word x y ↔
          (⟨i, x⟩ : Sigma X) = ⟨j, y⟩ := by
  induction word with
  | nil i =>
      intro _ x y
      change x = y ↔
        (⟨i, x⟩ : Sigma X) = ⟨i, y⟩
      constructor
      · intro h
        subst y
        rfl
      · intro h
        simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h
  | identity tail ih =>
      intro h x y
      exact ih h x y
  | atom a tail ih =>
      intro h
      simp [diversityLength] at h

/-- No zero-length word can impose an atom on two distinct tagged
real points. All actual word-profile constraints remain typed. -/
theorem zeroLength_distinct_impossible {i j : ι}
    (word : RawWord S i j)
    (hZero : diversityLength S word = 0)
    (x : X i) (y : X j)
    (hDistinct : (⟨i, x⟩ : Sigma X) ≠ ⟨j, y⟩) :
    ¬ RawWord.relation S word x y := by
  intro hxy
  exact hDistinct
    ((zeroLength_relation_iff_tagged_eq S word hZero x y).mp hxy)

end CCO.RawExact
