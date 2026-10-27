import CCO.RawExact.SortTrace

/-!
# B002 C12/C18: real vertex traces of represented RAW walks

A genuine semantic WordPath witness determines a list of actual
tagged real vertices. There is one real position per diversity
letter plus its endpoint, and identity letters add nothing.
The sort trace of these vertices is precisely the literal
original-sort trace of the RAW word, not a quotient sort.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Materialize the actual successive real points of one represented
word witness. Each recursive atomic letter prepends its SOURCE point.
The actual pair-colour along that letter is the witness' old atom. -/
def realWalkTrace {i j : ι} {word : RawWord S i j}
    {x : X i} {z : X j}
    (h : WordPath S word x z) : List (Sigma X) := by
  induction h with
  | nil x =>
      exact [⟨_, x⟩]
  | identity tail ih =>
      exact ih
  | atom a edge rest ih =>
      exact ⟨_, x⟩ :: ih

theorem realWalkTrace_length {i j : ι} {word : RawWord S i j}
    {x : X i} {z : X j} (h : WordPath S word x z) :
    (realWalkTrace S h).length = diversityLength S word + 1 := by
  induction h with
  | nil x => rfl
  | identity tail ih => exact ih
  | atom a edge rest ih =>
      simp only [realWalkTrace, List.length_cons, diversityLength, ih]
      omega

theorem realWalkTrace_sorts {i j : ι} {word : RawWord S i j}
    {x : X i} {z : X j} (h : WordPath S word x z) :
    (realWalkTrace S h).map Sigma.fst = wordSortTrace S word := by
  induction h with
  | nil x => rfl
  | identity tail ih => exact ih
  | atom a edge rest ih =>
      simp only [realWalkTrace, List.map_cons, wordSortTrace, ih]

end CCO.RawExact
