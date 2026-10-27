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

/-- Boolean root/middle bipartition; every theta edge flips sides. -/
def rootFlag (p : Fin 5) : Bool :=
  (p == 0) || (p == 1)

theorem adj_root_ne (p q : Fin 5) (h : Adj p q) :
    rootFlag p ≠ rootFlag q := by
  fin_cases p <;> fin_cases q <;>
    first | decide | (simp [Adj, middle] at h)

private theorem for_three :
    ∀ f : Fin 3 → Fin 5,
      Function.Injective f →
      (∀ p : Fin 3,
        Adj (f p) (f (cyclicNext (by decide) p))) →
        OmitsSomeMiddleFn f := by
  intro f _ hedges
  have odd3 : ∀ a b c : Bool,
      a ≠ b → b ≠ c → c ≠ a → False := by decide
  have h01 : rootFlag (f 0) ≠ rootFlag (f 1) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 0)
  have h12 : rootFlag (f 1) ≠ rootFlag (f 2) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 1)
  have h20 : rootFlag (f 2) ≠ rootFlag (f 0) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 2)
  exact False.elim (odd3 _ _ _ h01 h12 h20)

private theorem for_four :
    ∀ f : Fin 4 → Fin 5,
      Function.Injective f →
      (∀ p : Fin 4,
        Adj (f p) (f (cyclicNext (by decide) p))) →
        OmitsSomeMiddleFn f := by
  intro f _ hedges
  have toggle2 : ∀ a b c : Bool, a ≠ b → b ≠ c → a = c := by decide
  have two_miss : ∀ v w : Fin 5,
      ∃ t : Fin 3, v ≠ middle t ∧ w ≠ middle t := by decide
  have roots_not_mid : ∀ v : Fin 5, ∀ t : Fin 3,
      rootFlag v = true → v ≠ middle t := by decide
  have h01 : rootFlag (f 0) ≠ rootFlag (f 1) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 0)
  have h12 : rootFlag (f 1) ≠ rootFlag (f 2) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 1)
  have h23 : rootFlag (f 2) ≠ rootFlag (f 3) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 2)
  have h02 : rootFlag (f 0) = rootFlag (f 2) :=
    toggle2 _ _ _ h01 h12
  have h13 : rootFlag (f 1) = rootFlag (f 3) :=
    toggle2 _ _ _ h12 h23
  by_cases h0 : rootFlag (f 0) = true
  · have h2 : rootFlag (f 2) = true := h02.symm.trans h0
    obtain ⟨t, ht1, ht3⟩ := two_miss (f 1) (f 3)
    refine ⟨t, ?_⟩
    intro p
    fin_cases p
    · exact roots_not_mid (f 0) t h0
    · exact ht1
    · exact roots_not_mid (f 2) t h2
    · exact ht3
  · have h0false : rootFlag (f 0) = false := by
      cases h : rootFlag (f 0) <;> simp_all
    have h1true : rootFlag (f 1) = true := by
      cases h : rootFlag (f 1) <;> simp_all
    have h3true : rootFlag (f 3) = true := h13.symm.trans h1true
    obtain ⟨t, ht0, ht2⟩ := two_miss (f 0) (f 2)
    refine ⟨t, ?_⟩
    intro p
    fin_cases p
    · exact ht0
    · exact roots_not_mid (f 1) t h1true
    · exact ht2
    · exact roots_not_mid (f 3) t h3true

private theorem for_five :
    ∀ f : Fin 5 → Fin 5,
      Function.Injective f →
      (∀ p : Fin 5,
        Adj (f p) (f (cyclicNext (by decide) p))) →
        OmitsSomeMiddleFn f := by
  intro f _ hedges
  have odd5 : ∀ a b c d e : Bool,
      a ≠ b → b ≠ c → c ≠ d → d ≠ e → e ≠ a → False := by
    intro a b c d e h1 h2 h3 h4 h5
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> simp_all
  have h01 : rootFlag (f 0) ≠ rootFlag (f 1) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 0)
  have h12 : rootFlag (f 1) ≠ rootFlag (f 2) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 1)
  have h23 : rootFlag (f 2) ≠ rootFlag (f 3) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 2)
  have h34 : rootFlag (f 3) ≠ rootFlag (f 4) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 3)
  have h40 : rootFlag (f 4) ≠ rootFlag (f 0) := by
    simpa [cyclicNext] using adj_root_ne _ _ (hedges 4)
  exact False.elim (odd5 _ _ _ _ _ h01 h12 h23 h34 h40)

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
