import CCO.Finite
import Mathlib.Tactic

/-!
# B002 C06: finite theta skeleton, first nontrivial graph case

Three distinct two-edge private paths share precisely their two terminal
vertices. Their underlying simple graph is K_{2,3}. Every specified simple
cycle is a four-cycle through two private paths: at least one interior
vertex is absent. Here the finite combinatorial statement is checked
exhaustively over the concrete five-vertex graph; the path colours and
their actual homomorphisms are kept in a separate mathematical module.
No new CCO/Helly axiom is introduced.
-/

namespace CCO.RawExact.ThetaThree

/-- Distinct private middle vertices, all disjoint from the two roots. -/
def middle (t : Fin 3) : Fin 5 :=
  ⟨t.val + 2, by omega⟩

/-- Edges of the three private two-edge paths, without any parallel
edge or false root-to-root/diagonal adjacency. -/
def Adj (p q : Fin 5) : Prop :=
  ∃ t : Fin 3,
    ((p = 0 ∨ p = 1) ∧ q = middle t) ∨
    ((q = 0 ∨ q = 1) ∧ p = middle t)

instance (p q : Fin 5) : Decidable (Adj p q) := inferInstanceAs
  (Decidable (∃ t : Fin 3,
    ((p = 0 ∨ p = 1) ∧ q = middle t) ∨
    ((q = 0 ∨ q = 1) ∧ p = middle t)))

/-- A cycle admits a path whose private middle is not visited.
It is important that this is about *simple* cycles (injective f). -/
def OmitsSomeMiddleFn {n : Nat} (f : Fin n → Fin 5) : Prop :=
  ∃ t : Fin 3, ∀ p : Fin n, f p ≠ middle t

def OmitsSomeMiddle {n : Nat} (f : Fin n ↪ Fin 5) : Prop :=
  OmitsSomeMiddleFn f

/-- Enumerate all finite MAPS, rather than relying on a non-computable
decider for the type of embeddings. Injectivity is checked explicitly. -/
private theorem for_three :
    ∀ f : Fin 3 → Fin 5,
      Function.Injective f →
      (∀ p : Fin 3,
        Adj (f p) (f (cyclicNext (by decide) p))) →
        OmitsSomeMiddleFn f := by
  decide

private theorem for_four :
    ∀ f : Fin 4 → Fin 5,
      Function.Injective f →
      (∀ p : Fin 4,
        Adj (f p) (f (cyclicNext (by decide) p))) →
        OmitsSomeMiddleFn f := by
  decide

private theorem for_five :
    ∀ f : Fin 5 → Fin 5,
      Function.Injective f →
      (∀ p : Fin 5,
        Adj (f p) (f (cyclicNext (by decide) p))) →
        OmitsSomeMiddleFn f := by
  decide

/-- C06 cycle classification for the concrete three-by-two theta
graph. The general source C06 still needs arbitrary finite families
and arbitrary word lengths. -/
theorem every_simple_cycle_omits_middle
    {n : Nat} (hn : 3 ≤ n) (hpos : 0 < n)
    (f : Fin n ↪ Fin 5)
    (hedges : ∀ p : Fin n,
      Adj (f p) (f (cyclicNext hpos p))) :
    OmitsSomeMiddle f := by
  have bound : n ≤ 5 := by
    simpa using (Fintype.card_le_of_injective (fun p : Fin n => f p) f.injective)
  have hc : n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases hc with h3 | h4 | h5
  · subst n
    exact for_three (fun p => f p) f.injective hedges
  · subst n
    exact for_four (fun p => f p) f.injective hedges
  · subst n
    exact for_five (fun p => f p) f.injective hedges

end CCO.RawExact.ThetaThree
