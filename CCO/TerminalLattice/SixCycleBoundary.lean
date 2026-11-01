import CCO.TerminalLattice.FullCoverParity
import Mathlib.Tactic.Omega

/-!
# B050 C56: a genuine finite six-cycle shows why the FULL-cover hypothesis matters

The original C56 warns that a connected bipartite six-cycle has a
nontrivial intermediate even-walk equivalence, despite the upper
relation having index six. Its exact-length walk powers never fill
the upper relation. This finite check is formalized with the actual
six vertices, REAL undirected graph edges and arbitrarily long
walks, not just a bounded Python sanity test.

This is a boundary counterexample, not a proposed source model of
CCO/SAP or a weakening of the genuine full-cover power theorem.
-/

namespace CCO.TerminalLattice

/-- The literal undirected six-cycle with vertices 0,...,5. -/
def sixCycleAdj (a b : Fin 6) : Prop :=
  (a.val + 1) % 6 = b.val ∨ (b.val + 1) % 6 = a.val

/-- The real parity equivalence in the connected six-cycle. -/
def sixCycleEven (a b : Fin 6) : Prop :=
  a.val % 2 = b.val % 2

theorem sixCycleEven_equivalence : Equivalence sixCycleEven := by
  refine ⟨?_, ?_, ?_⟩
  · intro a
    rfl
  · intro a b h
    exact h.symm
  · intro a b c hab hbc
    exact hab.trans hbc

/-- It is strictly above equality and strictly below the indiscrete
upper equivalence. In particular the six-cycle is not a FULL cover. -/
theorem sixCycleEven_proper_intermediate :
    (∃ a b : Fin 6, a ≠ b ∧ sixCycleEven a b) ∧
    (∃ a b : Fin 6, ¬ sixCycleEven a b) := by
  constructor
  · exact ⟨0,2,by decide,by decide⟩
  · exact ⟨0,1,by decide⟩

theorem sixCycleAdj_symm (a b : Fin 6) :
    sixCycleAdj a b → sixCycleAdj b a := by
  intro h
  rcases h with h | h
  · exact Or.inr h
  · exact Or.inl h

/-- Every actual six-cycle edge flips parity; hence bipartiteness
is an explicit finite theorem rather than a diagrammatic assertion. -/
theorem sixCycleAdj_flips :
    ∀ a b : Fin 6, sixCycleAdj a b → ¬ sixCycleEven a b := by
  decide

/-- Exactly n ORIGINAL graph edges form a real finite walk;
in particular, no equality edge is inserted for positive powers. -/
def sixCycleWalk : Nat → Fin 6 → Fin 6 → Prop
  | 0, a, b => a = b
  | n + 1, a, b =>
      ∃ c : Fin 6, sixCycleAdj a c ∧ sixCycleWalk n c b

/-- All six vertices lie in ONE connected component: every ordered
pair is joined by some actual walk of length at most five. The
quantifier is over Fin 6, so this check is finite and kernel-reduced. -/
theorem sixCycle_connected :
    ∀ a b : Fin 6, ∃ n : Fin 6, sixCycleWalk n.val a b := by
  decide

/-- Parity is exactly the genuine even-walk equivalence on all
six vertices, not just an abstract two-colouring. -/
theorem sixCycle_evenWalk_eq_parity :
    ∀ a b : Fin 6, sixCycleEven a b ↔
      ∃ n : Fin 6, Even n.val ∧ sixCycleWalk n.val a b := by
  decide

/-- Every genuine length-n walk has parity difference equal to n.
The induction treats ALL n, not only small finite test exponents. -/
theorem sixCycleWalk_parity (n : Nat) (a b : Fin 6)
    (h : sixCycleWalk n a b) :
    (a.val % 2 + n % 2) % 2 = b.val % 2 := by
  induction n generalizing a b with
  | zero =>
      change a = b at h
      subst b
      simp
  | succ n ih =>
      change ∃ c : Fin 6, sixCycleAdj a c ∧ sixCycleWalk n c b at h
      obtain ⟨c,hAdj,hRest⟩ := h
      have hFlip : a.val % 2 ≠ c.val % 2 :=
        sixCycleAdj_flips a c hAdj
      have hC : (c.val % 2 + n % 2) % 2 = b.val % 2 :=
        ih c b hRest
      omega

/-- At EVERY length n some original pair remains inaccessible.
Therefore no large positive power ever becomes the complete
six-by-six upper relation, although the graph is connected. -/
theorem sixCycle_no_full_power (n : Nat) :
    ¬ ∀ a b : Fin 6, sixCycleWalk n a b := by
  intro hall
  have h00 := sixCycleWalk_parity n 0 0 (hall 0 0)
  have h01 := sixCycleWalk_parity n 0 1 (hall 0 1)
  omega

theorem sixCycle_no_eventual_full_powers :
    ¬ ∃ N : Nat, ∀ n : Nat, N ≤ n →
      ∀ a b : Fin 6, sixCycleWalk n a b := by
  rintro ⟨N,hN⟩
  exact sixCycle_no_full_power N (hN N le_rfl)

end CCO.TerminalLattice
