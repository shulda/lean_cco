import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Fin.Basic

/-! The higher-support obstruction in B048 C32. Every proper three-point
factor of the four-point complete 3-hypergraph is allowed, although the
whole declared diagram has no completion in the K₄³-free class. -/

universe u v
namespace CCO.FullPhaseLift.Boundary

abbrev TripleRelation (V : Type u) := V → V → V → Prop

/-- A four-clique means all ordered triples of distinct vertices occur. -/
def K4Free {V : Type u} (R : TripleRelation V) : Prop :=
  ∀ (f : Fin 4 → V), Function.Injective f →
    ¬ ∀ i j k, i ≠ j → i ≠ k → j ≠ k → R (f i) (f j) (f k)

def completeTriple (V : Type u) : TripleRelation V :=
  fun x y z => x ≠ y ∧ x ≠ z ∧ y ≠ z

/-- This is a hereditary class: every induced restriction remains free. -/
theorem K4Free.pullback {V : Type u} {W : Type v} {R : TripleRelation W}
    (h : K4Free R) (e : V ↪ W) :
    K4Free (fun x y z => R (e x) (e y) (e z)) := by
  intro f hf
  exact h (e ∘ f) (e.injective.comp hf)

theorem k4Free_of_card_le_three {V : Type u} [Fintype V]
    (hc : Fintype.card V ≤ 3) (R : TripleRelation V) : K4Free R := by
  intro f hf
  have hfour := Fintype.card_le_of_injective f hf
  have hbad : 4 ≤ 3 := (by simpa using hfour : 4 ≤ Fintype.card V).trans hc
  exact ((Nat.not_succ_le_self 3) hbad).elim

theorem complete_three_allowed : K4Free (completeTriple (Fin 3)) :=
  k4Free_of_card_le_three (by simp) _

theorem complete_four_forbidden : ¬ K4Free (completeTriple (Fin 4)) := by
  intro h
  exact h id Function.injective_id (fun _ _ _ hij hik hjk => ⟨hij,hik,hjk⟩)

/-- The four distinguished full factors, each omitting one vertex. -/
abbrev Factor (i : Fin 4) := {x : Fin 4 // x ≠ i}

theorem factor_card (i : Fin 4) : Fintype.card (Factor i) = 3 := by
  exact (Fintype.card_congr (finSuccAboveEquiv i)).symm

theorem each_frozen_factor_allowed (i : Fin 4) :
    K4Free (fun x y z : Factor i => completeTriple (Fin 4) x.val y.val z.val) :=
  k4Free_of_card_le_three (by rw [factor_card]) _

/-- Every arity-three tuple, including repeated-argument tuples, is
contained in one of the four complete factors. -/
theorem every_tuple_in_factor (xs : Fin 3 → Fin 4) :
    ∃ i : Fin 4, ∀ j, xs j ≠ i := by
  classical
  by_contra hn
  have hs : Function.Surjective xs := by
    intro i
    by_contra hi
    exact hn ⟨i,fun j hj => hi ⟨j,hj⟩⟩
  have hcard := Fintype.card_le_of_surjective xs hs
  simp at hcard

/-- Even an initially homomorphic completion cannot realize all four
positive triples once its complete pair diagram separates all vertices. -/
theorem no_injective_full_completion {W : Type u} {R : TripleRelation W}
    (hfree : K4Free R) (f : Fin 4 → W) (hinj : Function.Injective f)
    (hpos : ∀ i j k, completeTriple (Fin 4) i j k → R (f i) (f j) (f k)) : False :=
  hfree f hinj (fun _ _ _ hij hik hjk => hpos _ _ _ ⟨hij,hik,hjk⟩)

/-- Empty higher relations supply an old object of every finite size, so
their pair shadows put no bound on the cardinality of the chosen target. -/
theorem empty_higher_allowed (V : Type u) :
    K4Free (fun (_ _ _ : V) => False) := by
  intro f _ h
  exact h 0 1 2 (by decide) (by decide) (by decide)

end CCO.FullPhaseLift.Boundary
