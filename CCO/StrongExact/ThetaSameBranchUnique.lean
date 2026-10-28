import CCO.StrongExact.ThetaLineRankExtra
import CCO.StrongExact.ThetaArcWitness

/-!
# C07: ordered colour uniqueness inside one private theta branch

Each ordered pair of vertices in one private positive-word path
carries at most one oriented original diversity letter (or its
converse), even if the same sort occurs at both endpoints.
Forward/forward and reverse/reverse duplicates have the same literal
edge index; opposite orientations cannot form a two-cycle because
their integer ranks would increase in both directions.

Cross-branch uniqueness is separate: it uses disjoint private
interiors and the absence of direct root-to-root edges.
-/

universe u v w

namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- Two candidates of the SAME word branch with matching literal
ordered endpoints are equal as *fully typed atomic arcs*.
No propositional cast or assumed colour equality is needed. -/
theorem sameBranchArc_unique
    (ws : List (PositiveWord S i j)) (b : Fin ws.length)
    (arc₁ arc₂ : ThetaArc S ws)
    (he : ∃ e : wordEdgeIndex S (ws.get b),
       arc₁ = thetaForwardArc S ws b e ∨
       arc₁ = (thetaForwardArc S ws b e).reverse)
    (hf : ∃ f : wordEdgeIndex S (ws.get b),
       arc₂ = thetaForwardArc S ws b f ∨
       arc₂ = (thetaForwardArc S ws b f).reverse)
    (hSrc : arc₁.src = arc₂.src)
    (hDst : arc₁.dst = arc₂.dst) :
    arc₁ = arc₂ := by
  obtain ⟨e, he | he⟩ := he
  obtain ⟨f, hf | hf⟩ := hf
  · have h : thetaBranchEdgeSource S ws b e =
          thetaBranchEdgeSource S ws b f := by
      simpa [he, hf, thetaForwardArc] using hSrc
    have hef := thetaBranchEdgeSource_injective S ws b h
    subst f
    exact he.trans hf.symm
  · exfalso
    have h1 : thetaBranchEdgeSource S ws b e =
        thetaBranchEdgeTarget S ws b f := by
      simpa [he, hf, thetaForwardArc, ThetaArc.reverse] using hSrc
    have h2 : thetaBranchEdgeTarget S ws b e =
        thetaBranchEdgeSource S ws b f := by
      simpa [he, hf, thetaForwardArc, ThetaArc.reverse] using hDst
    exact thetaBranchEdge_no_reversed_pair S ws b e f ⟨h1,h2⟩
  · exfalso
    have h1 : thetaBranchEdgeSource S ws b f =
        thetaBranchEdgeTarget S ws b e := by
      simpa [he, hf, thetaForwardArc, ThetaArc.reverse] using hSrc.symm
    have h2 : thetaBranchEdgeTarget S ws b f =
        thetaBranchEdgeSource S ws b e := by
      simpa [he, hf, thetaForwardArc, ThetaArc.reverse] using hDst.symm
    exact thetaBranchEdge_no_reversed_pair S ws b f e ⟨h1,h2⟩
  · have h : thetaBranchEdgeTarget S ws b e =
          thetaBranchEdgeTarget S ws b f := by
      simpa [he, hf, thetaForwardArc, ThetaArc.reverse] using hSrc
    have hef := thetaBranchEdgeTarget_injective S ws b h
    subst f
    exact he.trans hf.symm

end CCO.StrongExact
