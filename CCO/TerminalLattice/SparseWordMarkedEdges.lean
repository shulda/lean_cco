import CCO.TerminalLattice.OptionalPositiveReadout
import CCO.TerminalLattice.SparseWordNetwork

/-!
# B050 C31–C35: the exact marked edges chosen by ONE old sparse-word network

All edges here are real canonical B002 `Edge` identifiers, not a
fictitious unoriented word index. The unique LAST centre is above
every root. One genuine OLD positive word is chosen on every spoke;
on genuine W graph edges we choose precisely the word indexed by
the ORIGINAL unordered `Sym2` graph label. A missing W edge has
no word occurrence, rather than a synthetic identity or Top atom.

These local selection lemmas bridge the actual old source diagram
readout with the existing full-G orbital profile and reset receiving
API, without assuming a global CCO completion.
-/

universe u v w t

namespace CCO.TerminalLattice

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {G : Type t} [Group G] [∀ j : ι, MulAction G (X j)]

/-- The canonical oriented marked edge from a real graph root to the
last centre. The inequality is the actual old finite vertex order. -/
def oldSparseSpokeMarkedEdge {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (v : Fin W.size) :
    CCO.RawExact.QuotientExpansion.Edge (W.size+1) :=
  ⟨(oldSparseRoot W v, oldSparseCentre W), by
    change v.val < W.size
    exact v.isLt⟩

/-- The canonical old marked edge between the two graph roots
x<y. No additional graph adjacency is assumed at this type level. -/
def oldSparseGraphMarkedEdge {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (x y : Fin W.size) (hxy : x < y) :
    CCO.RawExact.QuotientExpansion.Edge (W.size+1) :=
  ⟨(oldSparseRoot W x, oldSparseRoot W y), by
    change x.val < y.val
    exact hxy⟩

/-- The same old positive K-diversity word is genuinely present on
EVERY centre spoke, with orientation from root TO centre. -/
theorem oldSparseWordSelection_spoke
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (v : Fin W.size) :
    oldSparseWordSelection S W spoke words
      (oldSparseSpokeMarkedEdge W v) = some spoke := by
  classical
  simp [oldSparseWordSelection, oldSparseSpokeMarkedEdge,
    oldSparseRoot, oldSparseCentre]

/-- Every ACTUAL ascending W graph edge has exactly its genuine
unordered-edge label's original word (not merely a fine subset of a
complete quotient orbital). -/
theorem oldSparseWordSelection_graph
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (x y : Fin W.size) (hxy : x < y)
    (hAdj : W.graph.Adj x y) :
    oldSparseWordSelection S W spoke words
      (oldSparseGraphMarkedEdge W x y hxy) =
        some (words (W.label s(x,y))) := by
  classical
  have hNoCentre :
      (oldSparseGraphMarkedEdge W x y hxy).val.2.val ≠ W.size := by
    change y.val ≠ W.size
    exact Nat.ne_of_lt y.isLt
  simp [oldSparseWordSelection, oldSparseGraphMarkedEdge,
    oldSparseRoot, hNoCentre, hAdj]

/-- Absent W graph edges select NO old atomic word, proving directly
that their binary constraints really are unprescribed. -/
theorem oldSparseWordSelection_nonedge
    {i : ι} {q r g : Nat}
    (W : CCO.ParityHasse.Sparse.SparseLabelledGraph q r g)
    (spoke : PositiveWord S i i)
    (words : Fin r → PositiveWord S i i)
    (x y : Fin W.size) (hxy : x < y)
    (hNoAdj : ¬ W.graph.Adj x y) :
    oldSparseWordSelection S W spoke words
      (oldSparseGraphMarkedEdge W x y hxy) = none := by
  classical
  have hNoCentre :
      (oldSparseGraphMarkedEdge W x y hxy).val.2.val ≠ W.size := by
    change y.val ≠ W.size
    exact Nat.ne_of_lt y.isLt
  simp [oldSparseWordSelection, oldSparseGraphMarkedEdge,
    oldSparseRoot, hNoCentre, hNoAdj]

end CCO.TerminalLattice
