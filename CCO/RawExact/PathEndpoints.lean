import CCO.RawExact.SortTrace

/-!
# B002 C12: named original sorts at ends of every typed private path

The first finite path position is the actual source sort of its
RAW word. The last finite path position is the actual target sort.
Identity letters create no intermediate positions and preserve both
facts. These are needed to type the two attachments of a private
word path to the global root and to its old real marked centre.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

theorem pathSortAt_start {i j : ι}
    (word : RawWord S i j) :
    pathSortAt S word (pathStart S word) = i := by
  induction word with
  | nil i => rfl
  | identity tail ih =>
      simpa only [pathSortAt, pathStart, wordSortTrace,
        diversityLength] using ih
  | atom a tail ih =>
      simp [pathSortAt, pathStart, wordSortTrace, diversityLength]

theorem pathSortAt_finish {i j : ι}
    (word : RawWord S i j) :
    pathSortAt S word (pathFinish S word) = j := by
  induction word with
  | nil i => rfl
  | identity tail ih =>
      simpa only [pathSortAt, pathFinish, wordSortTrace,
        diversityLength] using ih
  | atom a tail ih =>
      simpa only [pathSortAt, pathFinish, wordSortTrace,
        diversityLength, List.get_cons_succ] using ih

end CCO.RawExact
