import CCO.RawExact.PrivatePaths

/-!
# B002 C12/C26: finite private RAW word-path skeletons

A typed RAW word supplies a finite path with one vertex per diversity
letter plus its final endpoint. Logical identity letters add *no*
vertices or edges. The endpoints retain their original named sorts.
The graph skeleton uses a genuinely undirected adjacency, without
parallel edges or an artificial diagonal. Colour-labelled path edges
and amalgamating several such private paths are separate obligations.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- The position set of the *reduced* path represented by a RAW word.
The head of an atomic letter is a new vertex; its tail positions are
disjoint from that head. An identity step creates no vertex. -/
def pathPositions {i j : ι} : RawWord S i j → Type (max u (max v w))
  | .nil _ => PUnit
  | .identity tail => pathPositions tail
  | .atom _ tail => Option (pathPositions tail)

instance pathPositions_finite {i j : ι}
    (word : RawWord S i j) : Finite (pathPositions S word) := by
  induction word with
  | nil _ => exact inferInstance
  | identity tail ih =>
      simpa only [pathPositions] using ih
  | atom a tail ih =>
      letI : Finite (pathPositions S tail) := ih
      change Finite (Option (pathPositions S tail))
      infer_instance

/-- Sort of a real path position, equal to the word's source sort
at its start and to its target sort at its end. -/
def pathSort {i j : ι} :
    (word : RawWord S i j) → pathPositions S word → ι
  | .nil _, _ => i
  | .identity tail, p => pathSort tail p
  | .atom _ _, none => i
  | .atom _ tail, some p => pathSort tail p

def pathStart {i j : ι} :
    (word : RawWord S i j) → pathPositions S word
  | .nil _ => PUnit.unit
  | .identity tail => pathStart tail
  | .atom _ _ => none

def pathFinish {i j : ι} :
    (word : RawWord S i j) → pathPositions S word
  | .nil _ => PUnit.unit
  | .identity tail => pathFinish tail
  | .atom _ tail => some (pathFinish tail)

theorem pathSort_start {i j : ι} (word : RawWord S i j) :
    pathSort S word (pathStart S word) = i := by
  induction word with
  | nil _ => rfl
  | identity tail ih => exact ih
  | atom _ _ => rfl

theorem pathSort_finish {i j : ι} (word : RawWord S i j) :
    pathSort S word (pathFinish S word) = j := by
  induction word with
  | nil _ => rfl
  | identity tail ih => exact ih
  | atom _ tail ih => exact ih

/-- Actual unlabelled edges of a private path. The new source vertex
meets precisely the old tail start; all other edges are inherited.
The construction has no extra identity or self-loop edge. -/
def pathAdjacent {i j : ι} :
    (word : RawWord S i j) →
      pathPositions S word → pathPositions S word → Prop
  | .nil _, _, _ => False
  | .identity tail, p, q => pathAdjacent tail p q
  | .atom _ _, none, none => False
  | .atom _ tail, none, some q => q = pathStart S tail
  | .atom _ tail, some p, none => p = pathStart S tail
  | .atom _ tail, some p, some q => pathAdjacent tail p q

theorem pathAdjacent_symm {i j : ι}
    (word : RawWord S i j)
    (p q : pathPositions S word) :
    pathAdjacent S word p q ↔ pathAdjacent S word q p := by
  induction word with
  | nil _ =>
      simp [pathAdjacent]
  | identity tail ih =>
      exact ih p q
  | atom a tail ih =>
      cases p with
      | none =>
          cases q with
          | none => simp [pathAdjacent]
          | some q => simp [pathAdjacent]
      | some p =>
          cases q with
          | none => simp [pathAdjacent]
          | some q => exact ih p q

theorem pathAdjacent_irrefl {i j : ι}
    (word : RawWord S i j)
    (p : pathPositions S word) :
    ¬ pathAdjacent S word p p := by
  induction word with
  | nil _ => simp [pathAdjacent]
  | identity tail ih => exact ih p
  | atom a tail ih =>
      cases p with
      | none => simp [pathAdjacent]
      | some p => exact ih p

/-- The first genuine atomic letter contributes exactly one undirected
edge, from the new source vertex to the previously existing tail start.
This includes the final zero-length tail without creating a loop. -/
theorem pathAdjacent_first {i j k : ι}
    (a : S.Atom i j) (tail : RawWord S j k) :
    pathAdjacent S (.atom a tail)
      none (some (pathStart S tail)) := by
  rfl

end CCO.RawExact
