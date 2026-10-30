import CCO.FiniteFibres.CycleWalks
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! C01 explicitly extracts the simple odd cycle in a non-bipartite atom
graph. Its purely graph-theoretic scope has no CCO/source hypothesis. -/
namespace CCO.FiniteFibres

theorem odd_closed_walk_has_odd_cycle {A : Type*} (K : SimpleGraph A)
    {x : A} (p : K.Walk x x) (hp : Odd p.length) :
    ∃ y,∃ q : K.Walk y y,q.IsCycle ∧ Odd q.length := by
  classical
  suffices h : ∀ n (x : A) (p : K.Walk x x),p.length = n → Odd n →
      ∃ y,∃ q : K.Walk y y,q.IsCycle ∧ Odd q.length by
    exact h p.length x p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x p hlen hodd
    cases p with
    | nil =>
      simp only [SimpleGraph.Walk.length_nil] at hlen
      subst n
      simp at hodd
    | @cons _ y _ e tail =>
      have htail : tail.length+1 = n := by simpa using hlen
      by_cases hpath : tail.IsPath
      · have hge : 3 ≤ (tail.cons e).length := by
          have hneq : y ≠ x := e.ne.symm
          have hpos : 0 < tail.length := by
            by_contra h
            have hz : tail.length = 0 := by omega
            exact hneq (SimpleGraph.Walk.eq_of_length_eq_zero (p := tail) hz)
          have hm : n%2 = 1 := Nat.odd_iff.mp hodd
          simp only [SimpleGraph.Walk.length_cons]
          omega
        exact ⟨x,tail.cons e,
          SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by simpa using hpath,hge⟩,
          hlen ▸ hodd⟩
      · have hex : ∃ z,∃ q : K.Walk z z,q.IsSubwalk tail ∧ ¬q.Nil := by
          by_contra hn
          push_neg at hn
          exact hpath (SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil.mpr hn)
        obtain ⟨z,q,hsub,hq⟩ := hex
        obtain ⟨r,s,hrs⟩ := hsub
        have hqpos : 0 < q.length := SimpleGraph.Walk.not_nil_iff_lt_length.mp hq
        have hlength : r.length+q.length+s.length+1 = n := by
          simpa only [hrs,SimpleGraph.Walk.length_append] using htail
        by_cases hqodd : Odd q.length
        · exact ih q.length (by omega) z q rfl hqodd
        · let short : K.Walk x x := (r.append s).cons e
          have hshort : short.length = r.length+s.length+1 := by simp [short]
          have hqeven : q.length%2 = 0 := Nat.even_iff.mp (Nat.not_odd_iff_even.mp hqodd)
          have hshortodd : Odd short.length := by
            apply Nat.odd_iff.mpr
            have := Nat.odd_iff.mp hodd
            omega
          exact ih short.length (by omega) x short rfl hshortodd

theorem not_bipartite_has_odd_cycle {A : Type*} (K : SimpleGraph A) (h : ¬K.IsBipartite) :
    ∃ y,∃ q : K.Walk y y,q.IsCycle ∧ Odd q.length := by
  classical
  have hex : ∃ x,∃ p : K.Walk x x,Odd p.length := by
    by_contra hn
    push_neg at hn
    exact h (no_odd_closed_walk_isBipartite K hn)
  obtain ⟨x,p,hp⟩ := hex
  exact odd_closed_walk_has_odd_cycle K p hp

theorem atom_cycle_obstruction {C : Type*} (T : Target C) (a : C)
    (h : ¬(atomGraph T a).IsBipartite) :
    ∃ x,∃ p : (atomGraph T a).Walk x x,
      p.IsCycle ∧ Odd p.length ∧ 3 ≤ p.length ∧ p.length ≤ T.size := by
  obtain ⟨x,p,hp,ho⟩ := not_bipartite_has_odd_cycle (atomGraph T a) h
  refine ⟨x,p,hp,ho,hp.three_le_length,?_⟩
  let f : Fin p.length → Fin T.size := fun j => p.getVert j.val
  have hi : Function.Injective f := by
    intro i j heq
    apply Fin.ext
    have him : i.val ∈ {k : Nat | k ≤ p.length-1} := by have := i.isLt; change i.val ≤ p.length-1; omega
    have hjm : j.val ∈ {k : Nat | k ≤ p.length-1} := by have := j.isLt; change j.val ≤ p.length-1; omega
    exact hp.getVert_injOn' him hjm heq
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hi

end CCO.FiniteFibres
