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
/-- The cyclic predecessor of the left root is also a private
word vertex. The old specified edge is read in reverse orientation. -/
theorem thetaCycle_left_prev_private
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (hp : C.vertices p = thetaLeft S ws) :
    ∃ b : Fin ws.length, ∃ t : wordInterior S (ws.get b),
      C.vertices (cyclicPrev C.length_pos p) =
        (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  let prev := cyclicPrev C.length_pos p
  have hAdj : thetaAdjacent S ws (C.vertices prev) (C.vertices p) := by
    have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices prev) (C.vertices (cyclicNext C.length_pos prev))
      (C.next_ne prev)).mp (C.specified prev)
    simpa only [prev, cyclicNext_prev] using he
  have hNotLeft : C.vertices prev ≠ thetaLeft S ws := by
    intro h
    apply C.next_ne prev
    calc
      C.vertices prev = thetaLeft S ws := h
      _ = C.vertices p := hp.symm
      _ = C.vertices (cyclicNext C.length_pos prev) := by
        simp only [prev, cyclicNext_prev]
  have hNotRight : C.vertices prev ≠ thetaRight S ws := by
    intro h
    have hBad : thetaAdjacent S ws (thetaLeft S ws)
        (thetaRight S ws) := by
      apply thetaAdjacent_symmetric S ws
      simpa only [h, hp] using hAdj
    exact thetaAdjacent_no_root_pair S ws hLong hBad
  exact thetaVertex_private_of_ne_roots S ws (C.vertices prev)
    hNotLeft hNotRight

/-- Symmetrically, a simple cycle cannot enter the right root
directly from the other root. -/
theorem thetaCycle_right_prev_private
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (hp : C.vertices p = thetaRight S ws) :
    ∃ b : Fin ws.length, ∃ t : wordInterior S (ws.get b),
      C.vertices (cyclicPrev C.length_pos p) =
        (.inr ⟨b,t⟩ : thetaVertices S ws) := by
  let prev := cyclicPrev C.length_pos p
  have hAdj : thetaAdjacent S ws (C.vertices prev) (C.vertices p) := by
    have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
      (C.vertices prev) (C.vertices (cyclicNext C.length_pos prev))
      (C.next_ne prev)).mp (C.specified prev)
    simpa only [prev, cyclicNext_prev] using he
  have hNotRight : C.vertices prev ≠ thetaRight S ws := by
    intro h
    apply C.next_ne prev
    calc
      C.vertices prev = thetaRight S ws := h
      _ = C.vertices p := hp.symm
      _ = C.vertices (cyclicNext C.length_pos prev) := by
        simp only [prev, cyclicNext_prev]
  have hNotLeft : C.vertices prev ≠ thetaLeft S ws := by
    intro h
    have hBad : thetaAdjacent S ws (thetaLeft S ws)
        (thetaRight S ws) := by
      simpa only [h, hp] using hAdj
    exact thetaAdjacent_no_root_pair S ws hLong hBad
  exact thetaVertex_private_of_ne_roots S ws (C.vertices prev)
    hNotLeft hNotRight


end CCO.StrongExact
