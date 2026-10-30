import Mathlib.Logic.Equiv.Fintype
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions
import Mathlib.Tactic.FinCases
import Lean.Elab.Tactic.Omega

/-!
# Actual ages of the finite complete graphs

The one-colour complete n-point model is determined by its vertex number.
Its induced embeddings are precisely injections, including the empty model.
The class n ≤ k has ordinary amalgamation: embed both sides in Kk and
align their root maps by an actual permutation of its finite carrier.
-/
namespace CCO.RelationalCompletion.Atomic.Boundaries

/-- The age of the one-colour complete graph on k vertices. -/
def CompleteAge (k n : Nat) : Prop := n ≤ k

/-- Actual embeddings amalgamate in a finite member of the same age.
The images need not intersect exactly in the base. -/
theorem completeAge_AP {k c a b : Nat} (ha : CompleteAge k a)
    (hb : CompleteAge k b) (eA : Fin c ↪ Fin a) (eB : Fin c ↪ Fin b) :
    ∃ (t : Nat), CompleteAge k t ∧
      ∃ (fA : Fin a ↪ Fin t) (fB : Fin b ↪ Fin t),
        ∀ x, fA (eA x) = fB (eB x) := by
  let iA : Fin a ↪ Fin k := Fin.castLEEmb ha
  let iB : Fin b ↪ Fin k := Fin.castLEEmb hb
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun x => iB (eB x)) (fun x => iA (eA x))
    (iB.injective.comp eB.injective) (iA.injective.comp eA.injective)
  exact ⟨k, le_rfl, iA, iB.trans σ.toEmbedding, fun x => (hσ x).symm⟩

/-- Every at-most-three-point complete induced submodel of K4 belongs to Age K3. -/
theorem complete_three_small (n : Nat) (hn : n ≤ 3) : CompleteAge 3 n := hn

/-- The complete four-point input is not in Age K3. -/
theorem complete_four_not_mem : ¬CompleteAge 3 4 := by unfold CompleteAge; omega

/-- A homomorphism between complete graphs is forced injective. -/
theorem completeGraph_hom_injective {a b : Nat}
    (f : SimpleGraph.completeGraph (Fin a) →g SimpleGraph.completeGraph (Fin b)) :
    Function.Injective f := by
  intro x y heq
  by_contra hne
  have h := f.map_rel' hne
  exact h heq

/-- K4 has no colour homomorphism into K3. -/
theorem no_K4_to_K3 :
    IsEmpty (SimpleGraph.completeGraph (Fin 4) →g SimpleGraph.completeGraph (Fin 3)) := by
  constructor
  intro f
  have h := Fintype.card_le_of_injective f (completeGraph_hom_injective f)
  simp at h

/-- Every simple m-cycle is homomorphically realizable in K3, for every m ≥ 3. -/
theorem every_cycle_three_colourable (m : Nat) (hm : 3 ≤ m) :
    Nonempty (SimpleGraph.cycleGraph m →g SimpleGraph.completeGraph (Fin 3)) :=
  ⟨SimpleGraph.cycleGraph.tricoloring m (by omega)⟩

/-- In particular a four-cycle fan may identify its opposite vertices. -/
def square_to_edge : SimpleGraph.cycleGraph 4 →g SimpleGraph.completeGraph (Fin 2) where
  toFun p := ⟨p.val % 2, Nat.mod_lt _ (by decide)⟩
  map_rel' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [SimpleGraph.cycleGraph_adj] <;> contradiction

 theorem square_to_edge_collision : square_to_edge 0 = square_to_edge 2 := rfl

end CCO.RelationalCompletion.Atomic.Boundaries
