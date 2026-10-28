import CCO.StrongExact.ThetaHomReadout

/-! Original-sort actual point sequence along each typed private theta branch.
The edge readout uses only old diversity labels, no new provider. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

noncomputable def thetaPointLine
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (f : DiagramHom ((thetaEdgesOfLong S ws hLong).toDiagram))
    (b : Fin ws.length) :
    ∀ p : wordPositions S (ws.get b),
      X (wordPositionSort S (ws.get b) p) :=
  fun p => (thetaBranchPosition_sort S ws b p) ▸
    f.point (thetaBranchPosition S ws b p)

/-- Every original positive letter is preserved by an arbitrary theta
homomorphism, after the two genuinely typed endpoint transports. -/
theorem thetaPointLine_letters
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (f : DiagramHom ((thetaEdgesOfLong S ws hLong).toDiagram))
    (b : Fin ws.length)
    (e : wordEdgeIndex S (ws.get b)) :
    S.colour
      (thetaPointLine S ws hLong f b (wordEdgeSource S (ws.get b) e))
      (thetaPointLine S ws hLong f b (wordEdgeTarget S (ws.get b) e)) =
      some (wordEdgeAtom S (ws.get b) e) := by
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
    (thetaBranchPosition_sort S ws b (wordEdgeSource S (ws.get b) e))
    (thetaBranchPosition_sort S ws b (wordEdgeTarget S (ws.get b) e))
    (wordEdgeAtom S (ws.get b) e)
    (f.point (thetaBranchPosition S ws b
      (wordEdgeSource S (ws.get b) e)))
    (f.point (thetaBranchPosition S ws b
      (wordEdgeTarget S (ws.get b) e))) he

end CCO.StrongExact
