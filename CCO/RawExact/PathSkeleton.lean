import CCO.RawExact.PrivatePaths
import Lean.Elab.Tactic.Omega

/-!
# B002 C12/C26: finite skeletons of genuine RAW word paths

Every diversity letter contributes one edge and one additional
position. A true identity letter contributes neither an edge nor a
position. At this first, purely combinatorial layer positions are
Fin (diversityLength + 1). The word itself still carries all original
typed atomic letters; matching position sorts, edge colours and
amalgamating multiple private paths are later proof obligations.
There are no parallel edges and no artificial equality edges.
-/

universe u v w

namespace CCO.RawExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)

/-- Count only real diversity edges; omit logical identity letters. -/
def diversityLength {i j : ι} : RawWord S i j → Nat
  | .nil _ => 0
  | .identity tail => diversityLength tail
  | .atom _ tail => diversityLength tail + 1

/-- Finite formal vertices of the genuine reduced private path. -/
abbrev PathPosition {i j : ι} (word : RawWord S i j) :=
  Fin (diversityLength S word + 1)

def pathStart {i j : ι} (word : RawWord S i j) :
    PathPosition S word :=
  ⟨0, Nat.zero_lt_succ _⟩

def pathFinish {i j : ι} (word : RawWord S i j) :
    PathPosition S word :=
  ⟨diversityLength S word, Nat.lt_succ_self _⟩

/-- Two path vertices share an edge iff their indices are successive.
This is an undirected simple graph with genuine positive-length edges. -/
def pathAdjacent {i j : ι}
    (word : RawWord S i j)
    (p q : PathPosition S word) : Prop :=
  p.val + 1 = q.val ∨ q.val + 1 = p.val

theorem diversityLength_nil (i : ι) :
    diversityLength S (.nil i) = 0 := rfl

theorem diversityLength_identity {i j : ι}
    (tail : RawWord S i j) :
    diversityLength S (.identity tail) = diversityLength S tail := rfl

theorem diversityLength_atom {i j k : ι}
    (a : S.Atom i j) (tail : RawWord S j k) :
    diversityLength S (.atom a tail) = diversityLength S tail + 1 := rfl

theorem pathAdjacent_symm {i j : ι}
    (word : RawWord S i j) (p q : PathPosition S word) :
    pathAdjacent S word p q ↔ pathAdjacent S word q p := by
  unfold pathAdjacent
  exact or_comm

theorem pathAdjacent_irrefl {i j : ι}
    (word : RawWord S i j) (p : PathPosition S word) :
    ¬ pathAdjacent S word p p := by
  unfold pathAdjacent
  omega

theorem pathAdjacent_ne {i j : ι}
    (word : RawWord S i j)
    (p q : PathPosition S word)
    (hpq : pathAdjacent S word p q) :
    p ≠ q := by
  intro heq
  subst q
  exact pathAdjacent_irrefl S word p hpq

/-- The first position can have only the next position as neighbour.
If the reduced word is empty there is no such position. -/
theorem pathAdjacent_start_iff {i j : ι}
    (word : RawWord S i j) (q : PathPosition S word) :
    pathAdjacent S word (pathStart S word) q ↔ q.val = 1 := by
  unfold pathAdjacent pathStart
  simp only
  omega

/-- The last position can have only the immediately preceding
position as neighbour, including the zero-length boundary. -/
theorem pathAdjacent_finish_iff {i j : ι}
    (word : RawWord S i j) (p : PathPosition S word) :
    pathAdjacent S word p (pathFinish S word) ↔
      p.val + 1 = diversityLength S word := by
  unfold pathAdjacent pathFinish
  simp only
  have hp := p.isLt
  omega

/-- Identity letters do not change the exact number of vertices. -/
theorem identity_path_positions {i j : ι}
    (word : RawWord S i j) :
    PathPosition S (.identity word) = PathPosition S word := by
  rfl

end CCO.RawExact
