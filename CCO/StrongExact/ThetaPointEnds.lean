import CCO.StrongExact.ThetaPointLine

/-! Explicit endpoint transport on each literal theta word line.
This avoids an ambiguous motive for transport through recursively
defined positive-word endpoint sorts. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- The first position of every private word is the SAME left root. -/
theorem thetaPointLine_source
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (f : DiagramHom ((thetaEdgesOfLong S ws hLong).toDiagram))
    (b : Fin ws.length) :
    Eq.mp (congrArg X (wordSource_sort S (ws.get b)))
      (thetaPointLine S ws hLong f b (wordSource S (ws.get b))) =
      f.point (thetaLeft S ws) := by
  exact cast_at_equal_vertex_mp (thetaVertexSort S ws) f.point
    (thetaBranchPosition_source S ws b)
    (thetaBranchPosition_sort S ws b (wordSource S (ws.get b)))
    (wordSource_sort S (ws.get b))

/-- The last position of every private word is the SAME right root. -/
theorem thetaPointLine_target
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (f : DiagramHom ((thetaEdgesOfLong S ws hLong).toDiagram))
    (b : Fin ws.length) :
    Eq.mp (congrArg X (wordTarget_sort S (ws.get b)))
      (thetaPointLine S ws hLong f b (wordTarget S (ws.get b))) =
      f.point (thetaRight S ws) := by
  exact cast_at_equal_vertex_mp (thetaVertexSort S ws) f.point
    (thetaBranchPosition_target S ws b)
    (thetaBranchPosition_sort S ws b (wordTarget S (ws.get b)))
    (wordTarget_sort S (ws.get b))

end CCO.StrongExact
