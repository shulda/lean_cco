import CCO.StrongExact.ThetaCycleRootPositions
import CCO.StrongExact.ThetaGraphBridge

/-! In long theta graphs, a simple-cycle root has no root neighbor.
Its immediate successor is therefore an actual private word position. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

private theorem thetaVertex_private_of_ne_roots
    (ws : List (PositiveWord S i j))
    (v : thetaVertices S ws)
    (hL : v ≠ thetaLeft S ws)
    (hR : v ≠ thetaRight S ws) :
    ∃ b : Fin ws.length, ∃ t : wordInterior S (ws.get b),
      v = (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  cases hv : v with
  | inl tag =>
      cases tag with
      | false =>
          exact False.elim (hL (by simpa only [thetaLeft] using hv))
      | true =>
          exact False.elim (hR (by simpa only [thetaRight] using hv))
  | inr z =>
      cases z with
      | mk b t =>
          exact ⟨b,t,rfl⟩

/-- The successor of the left root on a specified simple cycle is
a tagged private interior, not the right root or the left root. -/
theorem thetaCycle_left_next_private
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (hp : C.vertices p = thetaLeft S ws) :
    ∃ b : Fin ws.length, ∃ t : wordInterior S (ws.get b),
      C.vertices (cyclicNext C.length_pos p) =
        (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  let q := cyclicNext C.length_pos p
  have hAdj : thetaAdjacent S ws (C.vertices p) (C.vertices q) :=
    (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices p) (C.vertices q) (C.next_ne p)).mp (C.specified p)
  have hNotLeft : C.vertices q ≠ thetaLeft S ws := by
    intro h
    exact (C.next_ne p) (hp.trans h.symm)
  have hNotRight : C.vertices q ≠ thetaRight S ws := by
    intro h
    have hBad : thetaAdjacent S ws (thetaLeft S ws)
        (thetaRight S ws) := by
      simpa only [hp, h] using hAdj
    exact thetaAdjacent_no_root_pair S ws hLong hBad
  exact thetaVertex_private_of_ne_roots S ws (C.vertices q)
    hNotLeft hNotRight

/-- The same private-neighbor condition at the right root.
Root sorts may coincide; formal vertices remain distinct. -/
theorem thetaCycle_right_next_private
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (hp : C.vertices p = thetaRight S ws) :
    ∃ b : Fin ws.length, ∃ t : wordInterior S (ws.get b),
      C.vertices (cyclicNext C.length_pos p) =
        (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  let q := cyclicNext C.length_pos p
  have hAdj : thetaAdjacent S ws (C.vertices p) (C.vertices q) :=
    (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices p) (C.vertices q) (C.next_ne p)).mp (C.specified p)
  have hNotRight : C.vertices q ≠ thetaRight S ws := by
    intro h
    exact (C.next_ne p) (hp.trans h.symm)
  have hNotLeft : C.vertices q ≠ thetaLeft S ws := by
    intro h
    have hBad : thetaAdjacent S ws (thetaLeft S ws)
        (thetaRight S ws) := by
      apply thetaAdjacent_symmetric S ws
      simpa only [hp, h] using hAdj
    exact thetaAdjacent_no_root_pair S ws hLong hBad
  exact thetaVertex_private_of_ne_roots S ws (C.vertices q)
    hNotLeft hNotRight

end CCO.StrongExact
