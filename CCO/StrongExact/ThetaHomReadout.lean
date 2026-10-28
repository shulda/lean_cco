import CCO.StrongExact.ThetaGraphBridge
import CCO.StrongExact.ThetaWordLineReadout

/-!
# C07: every actual theta homomorphism reads each genuine private word

Each displayed letter in the selected finite typed theta diagram
is preserved by a diagram homomorphism. Transport that literal
word-line witness along the proven original-sort equalities at every
formal position and recover the entire represented positive word.

The same two formal root vertices are used for every branch. No
STRONG equality atom, SAP, hidden completion or new provider is used.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Each occurrence of a long positive word is represented by
the endpoints of any genuine theta-diagram homomorphism. -/
theorem thetaDiagramHom_represented_branch
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (f : DiagramHom ((thetaEdgesOfLong S ws hLong).toDiagram))
    (b : Fin ws.length) :
    PositiveWord.represented S (ws.get b)
      (f.point (thetaLeft S ws))
      (f.point (thetaRight S ws)) := by
  let point : ∀ p : wordPositions S (ws.get b),
      X (wordPositionSort S (ws.get b) p) :=
    fun p => (thetaBranchPosition_sort S ws b p) ▸
      f.point (thetaBranchPosition S ws b p)
  have hEdges : ∀ e : wordEdgeIndex S (ws.get b),
      S.colour (point (wordEdgeSource S (ws.get b) e))
        (point (wordEdgeTarget S (ws.get b) e)) =
        some (wordEdgeAtom S (ws.get b) e) := by
    intro e
    have he := thetaDiagramHom_respects_forward S ws hLong f b e
    simpa [point, thetaBranchEdgeSource, thetaBranchEdgeTarget,
      thetaBranchEdgeAtom] using he
  have hWord :=
    represented_of_literal_word_line S (ws.get b) point hEdges
  simpa [point, thetaBranchPosition_source, thetaBranchPosition_target,
    wordSource_sort, wordTarget_sort] using hWord

end CCO.StrongExact
