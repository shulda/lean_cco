import CCO.RawExact.RealTraceEndpoints
import CCO.RawExact.FanReferenceEdges
import Lean.Elab.Tactic.Omega

/-!
# B002 C12: indexed real points of arbitrary RAW word witnesses

The formal private fan previously indexed one independently chosen
reference witness for each word occurrence. For its cycle argument,
TWO witnesses must be replaced by pairwise-compatible old real
walks with the same chosen root.

These lemmas give index, original sort, endpoint and genuine-diversity
edge properties for ANY actual represented RAW WordPath, not only
the reference walk. Identity letters contribute no fake graph edge;
nonconsecutive actual points may coincide.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Actual old tagged point at any finite diversity position of
an arbitrary represented typed RAW word, with equality letters
already suppressed by its genuine real-walk trace. -/
def wordPathPointAt
    {i j : ι} {word : RawWord S i j}
    {x : X i} {y : X j}
    (path : WordPath S word x y)
    (p : PathPosition S word) : Sigma X :=
  (realWalkTrace S path).get ⟨p.val, by
    rw [realWalkTrace_length S path]
    exact p.isLt⟩

/-- Position sorts are determined by the original typed word,
independently of its old real walk realization. -/
theorem wordPathPointAt_sort
    {i j : ι} {word : RawWord S i j}
    {x : X i} {y : X j}
    (path : WordPath S word x y)
    (p : PathPosition S word) :
    (wordPathPointAt S path p).1 = pathSortAt S word p := by
  have hsort : (realWalkTrace S path).map Sigma.fst =
      wordSortTrace S word := realWalkTrace_sorts S path
  have hReal : p.val < (realWalkTrace S path).length := by
    rw [realWalkTrace_length S path]
    exact p.isLt
  have hSort : p.val < (wordSortTrace S word).length := by
    rw [wordSortTrace_length S word]
    exact p.isLt
  have hNat :
      ((realWalkTrace S path).map Sigma.fst)[p.val]? =
      (wordSortTrace S word)[p.val]? :=
    congrArg (fun l : List ι => l[p.val]?) hsort
  have hAt :
      ((realWalkTrace S path)[p.val]'hReal).1 =
      (wordSortTrace S word)[p.val]'hSort := by
    rw [List.getElem?_eq_getElem (by
      simpa only [List.length_map] using hReal)] at hNat
    rw [List.getElem?_eq_getElem hSort] at hNat
    exact Option.some.inj (by
      simpa only [List.getElem_map] using hNat)
  simpa only [wordPathPointAt, pathSortAt, List.get_eq_getElem] using hAt

/-- This arbitrary walk starts at precisely the specified old real
source point, including words with leading identity letters. -/
theorem wordPathPointAt_start
    {i j : ι} {word : RawWord S i j}
    {x : X i} {y : X j}
    (path : WordPath S word x y) :
    wordPathPointAt S path (pathStart S word) =
      (⟨i, x⟩ : Sigma X) := by
  have hFirst := realWalkTrace_first_tagged S path
  have hBound : 0 < (realWalkTrace S path).length := by
    rw [realWalkTrace_length S path]
    omega
  rw [List.getElem?_eq_getElem hBound] at hFirst
  have hAt := Option.some.inj hFirst
  simpa only [wordPathPointAt, pathStart, List.get_eq_getElem] using hAt

/-- Its last formal position is the literal old real target point.
A positive word with a logical identity OUTPUT is still allowed. -/
theorem wordPathPointAt_finish
    {i j : ι} {word : RawWord S i j}
    {x : X i} {y : X j}
    (path : WordPath S word x y) :
    wordPathPointAt S path (pathFinish S word) =
      (⟨j, y⟩ : Sigma X) := by
  have hLast := realWalkTrace_last_tagged S path
  have hBound : diversityLength S word <
      (realWalkTrace S path).length := by
    rw [realWalkTrace_length S path]
    omega
  rw [List.getElem?_eq_getElem hBound] at hLast
  have hAt := Option.some.inj hLast
  simpa only [wordPathPointAt, pathFinish, List.get_eq_getElem] using hAt

/-- Two consecutive forward positions of ANY real RAW walk
carry a genuine old diversity atom. -/
theorem wordPathPointAt_genuine_forward
    {i j : ι} {word : RawWord S i j}
    {x : X i} {y : X j}
    (path : WordPath S word x y)
    (p q : PathPosition S word)
    (hpq : p.val + 1 = q.val) :
    GenuineEdge S (wordPathPointAt S path p)
      (wordPathPointAt S path q) := by
  have hBound : p.val + 1 < (realWalkTrace S path).length := by
    rw [realWalkTrace_length S path]
    have hq := q.isLt
    omega
  have hGenuine := (List.isChain_iff_getElem.mp
    (realWordPath_isChain S path)) p.val hBound
  have hqVal : q.val = p.val + 1 := hpq.symm
  simpa only [wordPathPointAt, List.get_eq_getElem, hqVal] using hGenuine

/-- Actual RAW walk edges carry old diversity atoms in EITHER
orientation, respecting the genuine source converse law. -/
theorem wordPathPointAt_genuine_adjacent
    {i j : ι} {word : RawWord S i j}
    {x : X i} {y : X j}
    (path : WordPath S word x y)
    (p q : PathPosition S word)
    (hpq : pathAdjacent S word p q) :
    GenuineEdge S (wordPathPointAt S path p)
      (wordPathPointAt S path q) := by
  rcases (pathAdjacent_iff_step S word p q).mp hpq with
    hForward | hBackward
  · exact wordPathPointAt_genuine_forward S path p q hForward
  · exact genuineEdge_reverse S _ _
      (wordPathPointAt_genuine_forward S path q p hBackward)

end CCO.RawExact
