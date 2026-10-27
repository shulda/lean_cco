import CCO.RawExact.PathSkeleton

/-!
# B002 C12: original-sort traces of genuine private RAW paths

A typed RAW word carries a finite list of the original named sorts
visited along its diversity edges. Erasing identity letters does not
change either this trace or the path length. The trace has precisely
one more entry than the number of diversity letters. This makes the
finite PathSkeleton indexes available for future typed edge labelling.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Finite successive named original sorts, including both endpoints. -/
def wordSortTrace {i j : ι} : RawWord S i j → List ι
  | .nil _ => [i]
  | .identity tail => wordSortTrace tail
  | .atom _ tail => i :: wordSortTrace tail

theorem wordSortTrace_identity {i j : ι}
    (tail : RawWord S i j) :
    wordSortTrace S (.identity tail) = wordSortTrace S tail := rfl

theorem wordSortTrace_length {i j : ι}
    (word : RawWord S i j) :
    (wordSortTrace S word).length =
      diversityLength S word + 1 := by
  induction word with
  | nil _ => rfl
  | identity tail ih => exact ih
  | atom a tail ih =>
      simp only [wordSortTrace, List.length_cons, diversityLength, ih]

/-- Typed original-sort coordinate of a finite private-path position.
Unlike a fake equality edge, an identity letter leaves this index
unchanged, and all sort data come from the actual RawWord. -/
def pathSortAt {i j : ι}
    (word : RawWord S i j) (p : PathPosition S word) : ι :=
  (wordSortTrace S word).get ⟨p.val, by
    rw [wordSortTrace_length S word]
    exact p.isLt⟩

end CCO.RawExact
