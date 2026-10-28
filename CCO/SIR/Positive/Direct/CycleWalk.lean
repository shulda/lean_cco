import CCO.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! A graph-theoretic simple closed walk gives the literal specified simple
cycle required by the CCO interface. No cycle homomorphism is assumed here. -/

namespace CCO.SIR.Positive.Direct

universe u v w z

variable {ι : Type u} {X : ι → Type v} {S : AtomicSource.{u,v,w} ι X}
variable {V : Type z} (D : PartialDiagram S V)
variable {K : SimpleGraph V}

theorem closedWalk_next_getVert {x : V} (p : K.Walk x x) (hp : 0 < p.length)
    (n : Fin p.length) :
    p.getVert ((n.val + 1) % p.length) = p.getVert (n.val + 1) := by
  by_cases h : n.val + 1 < p.length
  · rw [Nat.mod_eq_of_lt h]
  · have heq : n.val + 1 = p.length := by omega
    rw [heq, Nat.mod_self, SimpleGraph.Walk.getVert_zero,
      SimpleGraph.Walk.getVert_length]

/-- The graph must consist of genuinely specified edges of `D`. -/
noncomputable def cycleOfWalk
    (hK : ∀ x y, K.Adj x y → ∃ (h : x ≠ y), ∃ a, D.edge x y h = some a)
    {x : V} (p : K.Walk x x) (hc : p.IsCycle) : SimpleCycle D := by
  let hp : 0 < p.length := lt_of_lt_of_le (by decide : 0 < 3) hc.three_le_length
  let vertices : Fin p.length ↪ V := {
    toFun := fun n => p.getVert n.val
    inj' := by
      intro i j hij
      apply Fin.ext
      exact hc.getVert_injOn'
        (by change i.val ≤ p.length - 1; omega)
        (by change j.val ≤ p.length - 1; omega) hij
  }
  have hadj (n : Fin p.length) :
      K.Adj (vertices n) (vertices (cyclicNext hp n)) := by
    change K.Adj (p.getVert n.val) (p.getVert ((n.val + 1) % p.length))
    rw [closedWalk_next_getVert p hp n]
    exact p.adj_getVert_succ n.isLt
  exact {
    length := p.length
    length_ge_three := hc.three_le_length
    length_pos := hp
    vertices := vertices
    next_ne := fun n => (hadj n).ne
    specified := fun n => by
      obtain ⟨hne, a, ha⟩ := hK _ _ (hadj n)
      exact ⟨a, ha⟩
  }

@[simp] theorem cycleOfWalk_vertices
    (hK : ∀ x y, K.Adj x y → ∃ (h : x ≠ y), ∃ a, D.edge x y h = some a)
    {x : V} (p : K.Walk x x) (hc : p.IsCycle) (n : Fin p.length) :
    (cycleOfWalk D hK p hc).vertices n = p.getVert n.val := rfl

end CCO.SIR.Positive.Direct
