import CCO.StrongExact.ThetaGraphBridge
import CCO.StrongExact.ThetaWordLineReadout

/-!
# C07: homomorphic readout of every original typed theta branch

For every genuinely specified diversity letter the selected theta
diagram stores exactly the old letter after its two necessary sort
transports. A homomorphism respecting these old edges therefore
realizes every private positive word between the SAME shared roots.
No injectivity, CCO, SAP, or pseudoidentity is assumed.
-/

universe u v w a

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Retype BOTH actual real endpoints and their old diversity atom
using exactly the same two original named-sort equalities. -/
private theorem colour_cast_both
    {s t s' t' : ι}
    (hs : s = s') (ht : t = t')
    (a : S.Atom s' t') (x : X s) (y : X t)
    (hxy : S.colour x y =
      some (hs.symm ▸ (ht.symm ▸ a))) :
    S.colour (hs ▸ x) (ht ▸ y) = some a := by
  cases hs
  cases ht
  simpa using hxy

/-- The two chained dependent sort casts cancel on two formal
positions identified as the SAME vertex, even when their equality
proofs were constructed by unrelated reductions. -/
private theorem cast_at_equal_vertex
    {α : Type a} (sort : α → ι)
    (point : ∀ x : α, X (sort x))
    {x y : α} {t : ι}
    (hxy : x = y) (hs : sort x = t) (ht : t = sort y) :
    ht ▸ (hs ▸ point x) = point y := by
  cases hxy
  cases hs
  cases ht
  rfl

/-- Every homomorphism of the actual long theta diagram carries
each complete original positive-word branch from the common left
root to the common right root, with no conditional provider. -/
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
    change S.colour
      (f.point (thetaBranchPosition S ws b
        (wordEdgeSource S (ws.get b) e)))
      (f.point (thetaBranchPosition S ws b
        (wordEdgeTarget S (ws.get b) e))) =
      some (thetaBranchEdgeAtom S ws b e) at he
    rw [thetaBranchEdgeAtom_cast S ws b e] at he
    change S.colour
      ((thetaBranchPosition_sort S ws b
        (wordEdgeSource S (ws.get b) e)) ▸
        f.point (thetaBranchPosition S ws b
          (wordEdgeSource S (ws.get b) e)))
      ((thetaBranchPosition_sort S ws b
        (wordEdgeTarget S (ws.get b) e)) ▸
        f.point (thetaBranchPosition S ws b
          (wordEdgeTarget S (ws.get b) e))) =
      some (wordEdgeAtom S (ws.get b) e)
    exact colour_cast_both S
      (thetaBranchPosition_sort S ws b
        (wordEdgeSource S (ws.get b) e))
      (thetaBranchPosition_sort S ws b
        (wordEdgeTarget S (ws.get b) e))
      (wordEdgeAtom S (ws.get b) e)
      (f.point (thetaBranchPosition S ws b
        (wordEdgeSource S (ws.get b) e)))
      (f.point (thetaBranchPosition S ws b
        (wordEdgeTarget S (ws.get b) e))) he
  have hWord :=
    represented_of_literal_word_line S (ws.get b) point hEdges
  have hStart :
      ((wordSource_sort S (ws.get b)) ▸
        point (wordSource S (ws.get b))) =
        f.point (thetaLeft S ws) := by
    change (wordSource_sort S (ws.get b)) ▸
      ((thetaBranchPosition_sort S ws b
        (wordSource S (ws.get b))) ▸
        f.point (thetaBranchPosition S ws b
          (wordSource S (ws.get b)))) =
      f.point (thetaLeft S ws)
    exact cast_at_equal_vertex S (thetaVertexSort S ws) f.point
      (thetaBranchPosition_source S ws b)
      (thetaBranchPosition_sort S ws b
        (wordSource S (ws.get b)))
      (wordSource_sort S (ws.get b))
  have hEnd :
      ((wordTarget_sort S (ws.get b)) ▸
        point (wordTarget S (ws.get b))) =
        f.point (thetaRight S ws) := by
    change (wordTarget_sort S (ws.get b)) ▸
      ((thetaBranchPosition_sort S ws b
        (wordTarget S (ws.get b))) ▸
        f.point (thetaBranchPosition S ws b
          (wordTarget S (ws.get b)))) =
      f.point (thetaRight S ws)
    exact cast_at_equal_vertex S (thetaVertexSort S ws) f.point
      (thetaBranchPosition_target S ws b)
      (thetaBranchPosition_sort S ws b
        (wordTarget S (ws.get b)))
      (wordTarget_sort S (ws.get b))
  simpa only [hStart, hEnd] using hWord

/-- The actual constructed diagram represents ALL its displayed
original positive words using the same literal root pair. -/
theorem thetaEdgesOfLong_representsWords
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws) :
    (thetaEdgesOfLong S ws hLong).RepresentsWords := by
  intro f word hw
  obtain ⟨b, hb⟩ := List.mem_iff_get.mp hw
  subst word
  exact thetaDiagramHom_represented_branch S ws hLong f b

end CCO.StrongExact
