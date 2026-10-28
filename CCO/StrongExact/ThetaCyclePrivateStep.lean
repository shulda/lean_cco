import CCO.StrongExact.ThetaCycleRootNeighbors
import CCO.StrongExact.ThetaPrivateConnectivity

/-! A specified theta cycle cannot switch its original positive-word
occurrence while traversing two consecutive private vertices.
Every change of branch must pass through one of the two shared roots. -/

universe u v w
namespace CCO.StrongExact

variable {ι : Type u} {X : ι → Type v}
variable (S : AtomicSource.{u,v,w} ι X)
variable {i j : ι}

/-- A forward old cycle edge between two private theta vertices
preserves the literal word occurrence index. -/
theorem thetaCycle_private_next_same_branch
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (b c : Fin ws.length)
    (t : wordInterior S (ws.get b))
    (u : wordInterior S (ws.get c))
    (hp : C.vertices p =
      (.inr ⟨b,t⟩ : thetaVertices S ws))
    (hn : C.vertices (cyclicNext C.length_pos p) =
      (.inr ⟨c,u⟩ : thetaVertices S ws)) :
    b = c := by
  have he := (thetaEdgesOfLong_edge_iff_arc S ws hLong
    (C.vertices p) (C.vertices (cyclicNext C.length_pos p))
    (C.next_ne p)).mp (C.specified p)
  rw [hp,hn] at he
  exact privateTheta_adj_same_branch S ws ⟨b,t⟩ ⟨c,u⟩ he

/-- The same invariant holds when traversing a specified cycle
backward. No injective word representation is assumed. -/
theorem thetaCycle_private_prev_same_branch
    (ws : List (PositiveWord S i j))
    (hLong : ∀ a : S.Atom i j,
      (PositiveWord.single a : PositiveWord S i j) ∉ ws)
    (C : SimpleCycle ((thetaEdgesOfLong S ws hLong).toDiagram))
    (p : Fin C.length)
    (b c : Fin ws.length)
    (t : wordInterior S (ws.get b))
    (u : wordInterior S (ws.get c))
    (hp : C.vertices p =
      (.inr ⟨b,t⟩ : thetaVertices S ws))
    (hprev : C.vertices (cyclicPrev C.length_pos p) =
      (.inr ⟨c,u⟩ : thetaVertices S ws)) :
    b = c := by
  have hStep := thetaCycle_private_next_same_branch S ws hLong C
    (cyclicPrev C.length_pos p) c b u t hprev
      (by simpa only [cyclicNext_prev] using hp)
  exact hStep.symm

end CCO.StrongExact
