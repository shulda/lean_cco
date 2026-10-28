import CCO.RawExact.FanVariableReference
import CCO.RawExact.WalkColourAtIndex
import CCO.RawExact.TaggedColourConverse
import Mathlib.Tactic

/-!
# B002 C12: changing a RAW word walk preserves every old path-edge atom

Every genuine diversity edge of a typed RAW word has the same full
original pair-colour in ANY two actual realizations of that word,
even if their old roots and internal points differ. The equality
holds at each finite formal path position, in both orientations,
and includes identity letters as zero-length contributions only.

This makes it sound to replace precisely two reference private
paths by pairwise-common-root witnesses while preserving the
specific edge-colours in the permanent anchored-fan diagram.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Two represented old walks of the same RAW word have the same
full typed atomic colour on every FORWARD formal path edge. -/
theorem wordPathPointAt_forward_colour_independent
    {i j : ι} (word : RawWord S i j)
    {x x' : X i} {y y' : X j}
    (walk : WordPath S word x y)
    (walk' : WordPath S word x' y')
    (p q : PathPosition S word)
    (hpq : p.val + 1 = q.val) :
    taggedColour S
      (wordPathPointAt S walk p)
      (wordPathPointAt S walk q) =
    taggedColour S
      (wordPathPointAt S walk' p)
      (wordPathPointAt S walk' q) := by
  have hpBound : p.val < diversityLength S word := by
    have hq := q.isLt
    omega
  let k : Fin (diversityLength S word) := ⟨p.val, hpBound⟩
  have hIndex := wordPaths_tagged_edge_colour_eq S word walk walk' k
  have hqVal : q.val = p.val + 1 := hpq.symm
  simpa only [wordPathPointAt, List.get_eq_getElem, hqVal, k] using hIndex

/-- Two represented RAW word walks have exactly matching full
old typed pair colours in EITHER orientation of each formal edge. -/
theorem wordPathPointAt_adjacent_colour_independent
    {i j : ι} (word : RawWord S i j)
    {x x' : X i} {y y' : X j}
    (walk : WordPath S word x y)
    (walk' : WordPath S word x' y')
    (p q : PathPosition S word)
    (hpq : pathAdjacent S word p q) :
    taggedColour S
      (wordPathPointAt S walk p)
      (wordPathPointAt S walk q) =
    taggedColour S
      (wordPathPointAt S walk' p)
      (wordPathPointAt S walk' q) := by
  rcases (pathAdjacent_iff_step S word p q).mp hpq with
    hForward | hBackward
  · exact wordPathPointAt_forward_colour_independent
      S word walk walk' p q hForward
  · exact taggedColour_reverse_eq_of_eq S _ _ _ _
      (wordPathPointAt_forward_colour_independent
        S word walk walk' q p hBackward)

/-- The independently selected original reference walk fixes
the exact old colour of every edge in ANOTHER possible WordPath
of the same occurrence. Its literal actual root may differ. -/
theorem occurrence_walk_reference_edge_colours
    {G : Type*} [Group G] [∀ t : ι, MulAction G (X t)]
    (H : HomogeneousSource S G)
    {root : ι} {I : Type (max u v)} [Finite I]
    {sort : I → ι}
    (D : ∀ t : I, NonemptyExact S root (sort t))
    (centres : ∀ t : I, X (sort t))
    (o : WordOccurrence S D)
    {x : X root}
    (walk : WordPath S (occurrenceWord S D o) x (centres o.1))
    (p q : PathPosition S (occurrenceWord S D o))
    (hpq : pathAdjacent S (occurrenceWord S D o) p q) :
    taggedColour S
      (wordPathPointAt S walk p)
      (wordPathPointAt S walk q) =
    taggedColour S
      (referencePointAt S H D centres o p)
      (referencePointAt S H D centres o q) := by
  have hEq := wordPathPointAt_adjacent_colour_independent
    S (occurrenceWord S D o) walk
    (referenceOccurrenceWalk S H D centres o).2 p q hpq
  simpa only [wordPathPointAt, referencePointAt, List.get_eq_getElem] using hEq

end CCO.RawExact
