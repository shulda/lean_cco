import CCO.StrongExact.ThetaWordLineReadout

/-!
# C07: recover a fully typed literal word line from represented semantics

A represented positive word is a finite real walk whose successive
genuine diversity atoms have the original word's positional sorts.
Every such walk admits a family of original points indexed by ALL
formal word positions, preserving every letter and both endpoints.
The path need not be injective; SAP injectivization remains separate.
No identity atom or extra mathematical assumption is introduced.
-/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Undo transport of a second original-sort point and its atomic
diversity letter. This is genuine type equality, not a new colour. -/
private theorem colour_uncast_second
    {i j k : ι} (h : k = j) (a : S.Atom i j)
    (x : X i) (y : X k)
    (hc : S.colour x (h ▸ y) = some a) :
    S.colour x y = some (h.symm ▸ a) := by
  cases h
  simpa using hc

/-- Convert the actual equality-inclusive represented positive word
relation into a literal sequence of old typed diversity letters.
Both real endpoint values are preserved, even on same-sort loops. -/
theorem literal_word_line_of_represented {i j : ι}
    (word : PositiveWord S i j) :
    ∀ (x : X i) (y : X j),
      PositiveWord.represented S word x y →
      ∃ point : ∀ p : wordPositions S word,
          X (wordPositionSort S word p),
        (∀ e : wordEdgeIndex S word,
          S.colour (point (wordEdgeSource S word e))
            (point (wordEdgeTarget S word e)) =
            some (wordEdgeAtom S word e)) ∧
        ((wordSource_sort S word) ▸ point (wordSource S word)) = x ∧
        ((wordTarget_sort S word) ▸ point (wordTarget S word)) = y := by
  induction word with
  | single a =>
      intro x y h
      let point : ∀ p : wordPositions S (PositiveWord.single a),
          X (wordPositionSort S (PositiveWord.single a) p) :=
        fun p => match p with
          | false => x
          | true => y
      refine ⟨point, ?_, ?_, ?_⟩
      · intro e
        cases e
        change S.colour x y = some a
        exact h
      · rfl
      · rfl
  | cons a tail ih =>
      intro x y h
      change ∃ mid : X _, S.colour x mid = some a ∧
        PositiveWord.represented S tail mid y at h
      obtain ⟨mid,hxy,hTail⟩ := h
      obtain ⟨tailPoint,hEdges,hSource,hTarget⟩ := ih mid y hTail
      let point : ∀ p : wordPositions S (PositiveWord.cons a tail),
          X (wordPositionSort S (PositiveWord.cons a tail) p) :=
        fun p => match p with
          | none => x
          | some q => tailPoint q
      refine ⟨point, ?_, ?_, ?_⟩
      · intro e
        cases e with
        | inl _ =>
            change S.colour x (tailPoint (wordSource S tail)) =
              some ((wordSource_sort S tail).symm ▸ a)
            apply colour_uncast_second S (wordSource_sort S tail) a
              x (tailPoint (wordSource S tail))
            change S.colour x
              ((wordSource_sort S tail) ▸
                tailPoint (wordSource S tail)) = some a
            rw [hSource]
            exact hxy
        | inr e =>
            change S.colour
              (tailPoint (wordEdgeSource S tail e))
              (tailPoint (wordEdgeTarget S tail e)) =
                some (wordEdgeAtom S tail e)
            exact hEdges e
      · rfl
      · simpa only [point, wordTarget, wordTarget_sort,
          wordPositionSort] using hTarget

end CCO.StrongExact
