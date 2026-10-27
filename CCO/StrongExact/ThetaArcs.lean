import CCO.StrongExact.ThetaEdgeDistinct

/-!
# C07 finite typed theta arc list from actual diversity word letters

After the source's shared-root/private-vertex geometry and literal
edge endpoint injectivity, each positive-word letter becomes a
genuine old atomic diversity arc. Its reversed arc carries the
ACTUAL original converse atom, never a fake equality colour.

The complete collection of oriented arcs is finite because there
are finitely many words and every word has finitely many letters.
This is only the concrete finite arc *data* of the intended B001
partial diagram. Proving that it is simple, then classifying every
specified simple cycle, remains the explicit C07 obligation.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- A single genuinely typed, irreflexive, directed original atomic
edge in the finite shared-root theta graph. -/
structure ThetaArc (ws : List (PositiveWord S i j)) where
  src : thetaVertices S ws
  dst : thetaVertices S ws
  ne : src ≠ dst
  atom : S.Atom
    (thetaVertexSort S ws src)
    (thetaVertexSort S ws dst)

/-- Reverse one theta arc using only the original atomic converse. -/
def ThetaArc.reverse {ws : List (PositiveWord S i j)}
    (a : ThetaArc S ws) : ThetaArc S ws where
  src := a.dst
  dst := a.src
  ne := a.ne.symm
  atom := S.conv a.atom

/-- A single positive word letter inserted literally into the
shared-root theta graph, with the proof of distinct endpoints. -/
noncomputable def thetaForwardArc
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) : ThetaArc S ws where
  src := thetaBranchEdgeSource S ws b e
  dst := thetaBranchEdgeTarget S ws b e
  ne := thetaBranchEdge_distinct S ws b e
  atom := thetaBranchEdgeAtom S ws b e

/-- Finite list of all FORWARD diversity letters of a single private
theta branch, in a (noncanonical) enumeration of its finite edge type. -/
noncomputable def thetaBranchArcs
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length) : List (ThetaArc S ws) := by
  classical
  letI : Finite (wordEdgeIndex S (ws.get b)) :=
    finite_wordEdgeIndex S (ws.get b)
  letI : Fintype (wordEdgeIndex S (ws.get b)) :=
    Fintype.ofFinite _
  exact (Finset.univ : Finset (wordEdgeIndex S (ws.get b))).toList.map
    (thetaForwardArc S ws b)

/-- Every private old word letter appears in its theta arc list.
No quotient or global arbitrary orbit selector is needed. -/
theorem thetaForwardArc_mem_branch
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) :
    thetaForwardArc S ws b e ∈ thetaBranchArcs S ws b := by
  classical
  unfold thetaBranchArcs
  simp

/-- The whole finite theta candidate edge list, including literal
converses. A later theorem must check uniqueness of the atom
for each ordered distinct formal vertex pair before turning this
LIST into a single-valued B001 PartialDiagram.edge. -/
noncomputable def thetaArcs (ws : List (PositiveWord S i j)) :
    List (ThetaArc S ws) :=
  (List.finRange ws.length).flatMap
    (fun b => (thetaBranchArcs S ws b).flatMap
      (fun a => [a, a.reverse]))

end CCO.StrongExact
