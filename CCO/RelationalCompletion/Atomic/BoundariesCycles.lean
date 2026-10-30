import CCO.ParityHasse.Original.GraphBipartite
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Simple-cycle consistency really gives two-colourability

Every odd closed walk contains an odd simple cycle. The proof cuts out a
nonempty closed subwalk of a non-path tail and keeps the odd one of that
subwalk and its complement. Thus the cycle premise is not a disguised
bipartite-completion hypothesis.
-/

namespace CCO.RelationalCompletion.Atomic.Boundaries

open SimpleGraph

/-- Extract an actual odd simple cycle from an arbitrary odd closed walk. -/
theorem odd_closed_walk_has_odd_cycle {V : Type*} (G : SimpleGraph V)
    {x : V} (p : G.Walk x x) (hp : Odd p.length) :
    ∃ y, ∃ q : G.Walk y y, q.IsCycle ∧ Odd q.length := by
  classical
  suffices h : ∀ n (x : V) (p : G.Walk x x), p.length = n → Odd n →
      ∃ y, ∃ q : G.Walk y y, q.IsCycle ∧ Odd q.length by
    exact h p.length x p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x p hlen hodd
    cases p with
    | nil => simp only [SimpleGraph.Walk.length_nil] at hlen
             subst n
             simp at hodd
    | @cons _ y _ e tail =>
      have htail : tail.length + 1 = n := by simpa using hlen
      by_cases hpath : tail.IsPath
      · have hge : 3 ≤ (tail.cons e).length := by
          have hneq : y ≠ x := e.ne.symm
          have hpos : 0 < tail.length := by
            by_contra h
            have hz : tail.length = 0 := by omega
            exact hneq (SimpleGraph.Walk.eq_of_length_eq_zero (p := tail) hz)
          have hm : n % 2 = 1 := Nat.odd_iff.mp hodd
          simp only [SimpleGraph.Walk.length_cons]
          omega
        exact ⟨x, tail.cons e,
          SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hpath, hge⟩,
          hlen ▸ hodd⟩
      · have hex : ∃ z, ∃ q : G.Walk z z, q.IsSubwalk tail ∧ ¬q.Nil := by
          by_contra hn
          push Not at hn
          exact hpath (SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil.mpr hn)
        obtain ⟨z, q, hsub, hq⟩ := hex
        obtain ⟨r, s, hrs⟩ := hsub
        have hqpos : 0 < q.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hq
        have hlength : r.length + q.length + s.length + 1 = n := by
          simpa only [hrs, SimpleGraph.Walk.length_append] using htail
        by_cases hqodd : Odd q.length
        · exact ih q.length (by omega) z q rfl hqodd
        · let short : G.Walk x x := (r.append s).cons e
          have hshort : short.length = r.length + s.length + 1 := by
            simp [short]
          have hqeven : q.length % 2 = 0 := by
            have := Nat.not_odd_iff_even.mp hqodd
            exact Nat.even_iff.mp this
          have hshortodd : Odd short.length := by
            apply Nat.odd_iff.mpr
            have := Nat.odd_iff.mp hodd
            omega
          exact ih short.length (by omega) x short rfl hshortodd

/-- Absence of odd simple cycles suffices for an actual colouring into K2. -/
theorem no_odd_simple_cycle_isBipartite {V : Type*} (G : SimpleGraph V)
    (hcycle : ∀ x (p : G.Walk x x), p.IsCycle → ¬Odd p.length) : G.IsBipartite := by
  apply CCO.ParityHasse.Original.no_odd_closed_walk_isBipartite
  intro x p hp
  obtain ⟨y, q, hq, ho⟩ := odd_closed_walk_has_odd_cycle G p hp
  exact hcycle y q hq ho

end CCO.RelationalCompletion.Atomic.Boundaries
