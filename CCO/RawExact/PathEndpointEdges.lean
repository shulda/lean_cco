import CCO.RawExact.PathLocalDegree

/-!
# B002 C12/C26: only one-letter RAW paths produce direct fan edges

A positive reduced private path has source and target endpoints as
neighbours exactly when it consists of ONE genuine diversity atom.
For longer words every edge has an internal private vertex, so it
cannot collide with edges belonging to another word occurrence.
For a zero-length identity-only word there are no edges at all.

This is the precise combinatorial reduction behind the pinned
N05 instruction to merge duplicate direct edges of identical
atomic colour (rather than creating illegal parallel 2-cycles).
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- A direct source/target edge exists exactly for one diversity
letter; empty identity words have no edge, and longer paths have
private internal positions between their endpoints. -/
theorem pathAdjacent_endpoints_iff_single_atom {i j : ι}
    (word : RawWord S i j) :
    pathAdjacent S word (pathStart S word) (pathFinish S word) ↔
      diversityLength S word = 1 := by
  change (0 + 1 = diversityLength S word ∨
      diversityLength S word + 1 = 0) ↔
      diversityLength S word = 1
  omega

/-- If both endpoints of a genuine path edge are endpoints of
the whole word path, its length is exactly one. The reverse
orientation is permitted and no equality edge is introduced. -/
theorem pathAdjacent_endpoint_edge_is_single_atom {i j : ι}
    (word : RawWord S i j)
    (p q : PathPosition S word)
    (hp : p = pathStart S word ∨ p = pathFinish S word)
    (hq : q = pathStart S word ∨ q = pathFinish S word)
    (hadj : pathAdjacent S word p q) :
    diversityLength S word = 1 := by
  rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;>
    simp only [pathAdjacent, pathStart, pathFinish] at hadj <;>
    omega

/-- An actual one-letter RAW word has precisely one genuine
diversity edge and no extra identity edge. -/
theorem oneLetter_rawWord_atom {i j : ι} (a : S.Atom i j) :
    diversityLength S (.atom a (.nil j)) = 1 := rfl

end CCO.RawExact
