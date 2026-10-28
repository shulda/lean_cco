import CCO.StrongExact.ThetaPointEnds

/-! Complete semantic readout of every actual long theta branch.
This is a homomorphism theorem, not yet the missing cycle theorem. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Every theta homomorphism realizes each original positive branch
between the same two formal roots, even if they map to one real point. -/
theorem thetaDiagramHom_represented_branch
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (f : DiagramHom ((thetaEdgesOfLong S ws hLong).toDiagram))
    (b : Fin ws.length) :
    PositiveWord.represented S (ws.get b)
      (f.point (thetaLeft S ws)) (f.point (thetaRight S ws)) := by
  let point := thetaPointLine S ws hLong f b
  have hWord := represented_of_literal_word_line S (ws.get b) point
    (fun e => thetaPointLine_letters S ws hLong f b e)
  have hWordMp : PositiveWord.represented S (ws.get b)
      (Eq.mp (congrArg X (wordSource_sort S (ws.get b)))
        (point (wordSource S (ws.get b))))
      (Eq.mp (congrArg X (wordTarget_sort S (ws.get b)))
        (point (wordTarget S (ws.get b)))) := by
    simpa only [cast_eq_mp] using hWord
  dsimp only [point] at hWordMp
  rw [thetaPointLine_source S ws hLong f b,
      thetaPointLine_target S ws hLong f b] at hWordMp
  exact hWordMp

/-- The selected original-coloured private theta diagram represents
every word in its actual finite presentation, unconditionally. -/
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
