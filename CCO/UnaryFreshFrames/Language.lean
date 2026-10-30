import Mathlib.Data.Set.Image
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.GroupTheory.GroupAction.Defs
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Group.Subgroup.Actions

/-! Actual named typed unary structures. Extending a function by the identity
off its specified input sort is canonical bookkeeping; no off-sort value is
used by a well-sorted term. Relation symbols and sort sets need not be finite. -/
universe u v
namespace CCO.UnaryFreshFrames

structure Language where
  Sorts : Type u
  Func : Type u
  Rel : Type u
  input : Func → Sorts
  output : Func → Sorts
  arity : Rel → ℕ
  argument : (R : Rel) → Fin (arity R) → Sorts

inductive Term (L : Language.{u}) : L.Sorts → L.Sorts → Type u
  | id (s : L.Sorts) : Term L s s
  | func {s} (F : L.Func) (t : Term L s (L.input F)) : Term L s (L.output F)

def Term.comp {L : Language.{u}} {i j k : L.Sorts}
    (s : Term L j k) (t : Term L i j) : Term L i k :=
  match s with
  | .id _ => t
  | .func F s => .func F (s.comp t)

structure Structure (L : Language.{u}) (V : Type v) where
  sort : V → L.Sorts
  func : L.Func → V → V
  func_sort : ∀ F x, sort x = L.input F → sort (func F x) = L.output F
  func_offsort : ∀ F x, sort x ≠ L.input F → func F x = x
  rel : (R : L.Rel) → (Fin (L.arity R) → V) → Prop
  rel_sort : ∀ R xs, rel R xs → ∀ i, sort (xs i) = L.argument R i

namespace Structure
variable {L : Language.{u}} {V : Type v} (H : Structure L V)

def eval (C : Structure L V) {i j : L.Sorts} : Term L i j → V → V
  | .id _, x => x
  | .func F t, x => C.func F (eval C t x)

@[simp] theorem eval_id (i : L.Sorts) (x : V) : H.eval (.id i) x = x := rfl
@[simp] theorem eval_func {i : L.Sorts} (F : L.Func)
    (t : Term L i (L.input F)) (x : V) :
    H.eval (.func F t) x = H.func F (H.eval t x) := rfl

theorem eval_sort {i j : L.Sorts} (t : Term L i j) {x : V} (hx : H.sort x = i) :
    H.sort (H.eval t x) = j := by
  induction t with
  | id => exact hx
  | func F t ih => exact H.func_sort F _ ih

@[simp] theorem eval_comp {i j k : L.Sorts} (s : Term L j k)
    (t : Term L i j) (x : V) : H.eval (s.comp t) x = H.eval s (H.eval t x) := by
  induction s with
  | id => rfl
  | func F s ih => exact congrArg (H.func F) ih

def Closed (A : Set V) : Prop := ∀ F x, x ∈ A → H.func F x ∈ A

def closure (A : Set V) : Set V :=
  {y | ∃ x ∈ A, ∃ j : L.Sorts, ∃ t : Term L (H.sort x) j, H.eval t x = y}

def closureAt (x : V) : Set V := H.closure {x}

theorem subset_closure (A : Set V) : A ⊆ H.closure A := by
  intro x hx
  exact ⟨x, hx, H.sort x, .id _, rfl⟩

theorem eval_mem_closed {A : Set V} (hA : H.Closed A) {i j : L.Sorts}
    (t : Term L i j) {x : V} (hx : x ∈ A) : H.eval t x ∈ A := by
  induction t with
  | id => exact hx
  | func F t ih => exact hA F _ ih

theorem closure_minimal {A B : Set V} (hB : H.Closed B) (hAB : A ⊆ B) :
    H.closure A ⊆ B := by
  rintro y ⟨x, hx, j, t, rfl⟩
  exact H.eval_mem_closed hB t (hAB hx)

theorem closure_closed (A : Set V) : H.Closed (H.closure A) := by
  classical
  rintro F y hy
  rcases hy with ⟨x, hx, j, t, rfl⟩
  by_cases hs : H.sort (H.eval t x) = L.input F
  · have hj : j = L.input F := (H.eval_sort t rfl).symm.trans hs
    subst j
    exact ⟨x, hx, L.output F, .func F t, rfl⟩
  · rw [H.func_offsort F _ hs]
    exact ⟨x, hx, j, t, rfl⟩

theorem closure_eq {A : Set V} (hA : H.Closed A) : H.closure A = A :=
  Set.Subset.antisymm (H.closure_minimal hA (Set.Subset.refl A)) (H.subset_closure A)

theorem closure_mono {A B : Set V} (h : A ⊆ B) : H.closure A ⊆ H.closure B :=
  H.closure_minimal (H.closure_closed B) (h.trans (H.subset_closure B))

theorem closed_empty : H.Closed ∅ := fun _ _ h => False.elim h
theorem closure_empty : H.closure ∅ = ∅ := H.closure_eq H.closed_empty

theorem closed_union {A B : Set V} (hA : H.Closed A) (hB : H.Closed B) :
    H.Closed (A ∪ B) := fun F x hx => hx.elim (fun h => Or.inl (hA F x h))
      (fun h => Or.inr (hB F x h))

theorem closure_union (A B : Set V) : H.closure (A ∪ B) = H.closure A ∪ H.closure B := by
  ext y
  constructor
  · rintro ⟨x, hx | hx, j, t, ht⟩
    · exact Or.inl ⟨x, hx, j, t, ht⟩
    · exact Or.inr ⟨x, hx, j, t, ht⟩
  · rintro (⟨x, hx, j, t, ht⟩ | ⟨x, hx, j, t, ht⟩)
    · exact ⟨x, Or.inl hx, j, t, ht⟩
    · exact ⟨x, Or.inr hx, j, t, ht⟩

theorem mem_closure_iff_singleton {A : Set V} {y : V} :
    y ∈ H.closure A ↔ ∃ x ∈ A, y ∈ H.closureAt x := by
  constructor
  · rintro ⟨x, hx, j, t, ht⟩
    exact ⟨x, hx, x, rfl, j, t, ht⟩
  · rintro ⟨x, hx, z, hz, j, t, ht⟩
    subst z
    exact ⟨x, hx, j, t, ht⟩

/-- The full group preserves EVERY actual named relation and total typed map. -/
def automorphisms : Subgroup (Equiv.Perm V) where
  carrier := {e | (∀ x, H.sort (e x) = H.sort x) ∧
    (∀ F x, e (H.func F x) = H.func F (e x)) ∧
    ∀ R xs, H.rel R (e ∘ xs) ↔ H.rel R xs}
  one_mem' := ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => Iff.rfl⟩
  mul_mem' := by
    rintro e f ⟨heS, heF, heR⟩ ⟨hfS, hfF, hfR⟩
    refine ⟨fun x => (heS (f x)).trans (hfS x), ?_, ?_⟩
    · intro F x
      exact (congrArg e (hfF F x)).trans (heF F (f x))
    · intro R xs
      exact (heR R (f ∘ xs)).trans (hfR R xs)
  inv_mem' := by
    rintro e ⟨heS, heF, heR⟩
    refine ⟨?_, ?_, ?_⟩
    · intro x
      exact (heS (e.symm x)).symm.trans (congrArg H.sort (e.apply_symm_apply x))
    · intro F x
      apply e.injective
      simpa using (heF F (e.symm x)).symm
    · intro R xs
      have he := heR R (e.symm ∘ xs)
      have hh : e ∘ (e.symm ∘ xs) = xs := funext fun i => e.apply_symm_apply (xs i)
      rw [hh] at he
      exact he.symm

abbrev Aut := H.automorphisms

theorem aut_sort (g : H.Aut) (x : V) : H.sort (g • x) = H.sort x := g.property.1 x
theorem aut_func (g : H.Aut) (F : L.Func) (x : V) :
    g • H.func F x = H.func F (g • x) := g.property.2.1 F x
theorem aut_rel (g : H.Aut) (R : L.Rel) (xs : Fin (L.arity R) → V) :
    H.rel R ((fun x => g • x) ∘ xs) ↔ H.rel R xs := g.property.2.2 R xs

theorem aut_eval (g : H.Aut) {i j : L.Sorts} (t : Term L i j) (x : V) :
    g • H.eval t x = H.eval t (g • x) := by
  induction t with
  | id => rfl
  | func F t ih => exact (H.aut_func g F _).trans (congrArg (H.func F) ih)

end Structure
end CCO.UnaryFreshFrames
