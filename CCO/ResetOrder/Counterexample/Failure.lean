import CCO.ResetOrder.Counterexample.AdversarialOrder
import Mathlib.Data.Fin.Basic

/-! The source is fixed once. The avoiding competitor is constructed for
EVERY finite base host, not merely for rectangular hosts or bounded examples. -/
namespace CCO.ResetOrder.Counterexample

private def patternQ (x : Fin 3) : Bool := decide (x.val < 2)

def patternBase : Nested (Fin 3) where
  P := Setoid.ker (fun _ : Fin 3 => ())
  Q := Setoid.ker patternQ
  refine := fun _ => rfl

def patternOrder : patternBase.ConvexOrder where
  order := inferInstance
  convexP := fun _ _ _ => rfl
  convexQ := by
    change ∀ {a b c : Fin 3}, a ≤ b → b ≤ c → patternQ a = patternQ c → patternQ a = patternQ b
    unfold patternQ
    decide

def patternNext : Fin 3 → Fin 3 := fun x => if x = 0 then 1 else 2

def patternSuccessor : patternOrder.Successor where
  next := patternNext
  sameP := fun _ => rfl
  le_next := by
    change ∀ x : Fin 3, x ≤ patternNext x
    unfold patternNext
    decide
  least := by
    change ∀ x y : Fin 3, (() = ()) → x < y → patternNext x ≤ y
    unfold patternNext
    decide
  strict := by
    change ∀ x : Fin 3, (∃ y : Fin 3, (() = ()) ∧ x < y) → x < patternNext x
    unfold patternNext
    decide

/-- Actual failure of the composite EP quantifier: a single three-point
expanded source is avoided by a legal expansion of EVERY finite base host. -/
theorem composite_EP_fails {X : Type*} [Finite X] (A : Nested X) :
    ∃ (o : A.ConvexOrder) (s : o.Successor),
      ¬ Nonempty (Nested.ConvexOrder.Successor.Embedding patternSuccessor s) := by
  refine ⟨A.adversarialOrder, Nested.ConvexOrder.finiteSuccessor _, ?_⟩
  rintro ⟨e⟩
  apply A.adversarial_no_pattern (Nested.ConvexOrder.finiteSuccessor _)
    ((e.lt_iff 0 1).mpr (show (0 : Fin 3) < 1 by decide))
    ((e.lt_iff 1 2).mpr (show (1 : Fin 3) < 2 by decide))
    ((e.p_iff 1 2).mpr rfl) ((e.q_iff 0 1).mpr rfl)
    (fun h => (show ¬ patternBase.Q.r 1 2 by change (true : Bool) ≠ false; decide) ((e.q_iff 1 2).mp h))
  · simpa [patternSuccessor, patternNext] using (e.map_next 1).symm
  · simpa [patternSuccessor, patternNext] using (e.map_next 2).symm

/-- The upper EP quantifier has the exact chosen old host: the source's own
ordered reduct. Every expansion of that host is the same successor structure. -/
theorem upper_EP_quantifier {X : Type*} {A : Nested X} (o : A.ConvexOrder)
    (s : o.Successor) : ∀ t : o.Successor,
      Nonempty (Nested.ConvexOrder.Successor.Embedding s t) := by
  intro t
  have h := t.unique s
  subst t
  exact ⟨Nested.ConvexOrder.Successor.Embedding.refl s⟩

end CCO.ResetOrder.Counterexample
