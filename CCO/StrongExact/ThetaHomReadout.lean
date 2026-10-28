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

/-- Transport two genuinely dependent original-sort endpoints AND their
atomic fine colour across the same pair of sort equalities. This is
only equality transport, never a STRONG identity atom. -/
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

/-- The private theta edge atom really is the twice-transported
ORIGINAL letter. The source already established the sort equalities
for each formal position. -/
private theorem thetaBranchEdgeAtom_eq_cast
    (ws : List (PositiveWord S i j))
    (b : Fin ws.length) (e : wordEdgeIndex S (ws.get b)) :
    thetaBranchEdgeAtom S ws b e =
      (thetaBranchPosition_sort S ws b
        (wordEdgeSource S (ws.get b) e)).symm ▸
        ((thetaBranchPosition_sort S ws b
          (wordEdgeTarget S (ws.get b) e)).symm ▸
          wordEdgeAtom S (ws.get b) e) := by
  rfl

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
    rw [thetaBranchEdgeAtom_eq_cast S ws b e] at he
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
      (f.point (thetaBranchEdgeSource S ws b e))
      (f.point (thetaBranchEdgeTarget S ws b e)) he
  have hWord :=
    represented_of_literal_word_line S (ws.get b) point hEdges
  have hStart :
      ((wordSource_sort S (ws.get b)) ▸
        point (wordSource S (ws.get b))) =
        f.point (thetaLeft S ws) := by
    simp [point, thetaBranchPosition_source, wordSource_sort, thetaLeft_sort]
  have hEnd :
      ((wordTarget_sort S (ws.get b)) ▸
        point (wordTarget S (ws.get b))) =
        f.point (thetaRight S ws) := by
    simp [point, thetaBranchPosition_target, wordTarget_sort, thetaRight_sort]
  rw [hStart,hEnd] at hWord
  exact hWord

end CCO.StrongExact
