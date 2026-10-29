import CCO.UnarySupport.LocalTheorem
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.FinCases

/-! Concrete finite languages for the scope counterexamples. -/
namespace CCO.UnarySupport.Boundaries
open Structure

abbrev relationalSignature {R : Type} [Finite R] (arity : R → ℕ) : Signature where
  Sorts := Unit
  Func := Empty
  Rel := R
  input := Empty.elim
  output := Empty.elim
  arity := arity
  argument _ _ := ()
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteRel := inferInstance

def relational {R : Type} [Finite R] (arity : R → ℕ) {V : Type}
    (r : (a : R) → (Fin (arity a) → V) → Prop) : Structure (relationalSignature arity) V where
  sort _ := ()
  func F := Empty.elim F
  functional F := Empty.elim F
  func_sorted F := Empty.elim F
  rel := r
  rel_sorted _ _ _ _ := rfl

theorem relational_closed {R : Type} [Finite R] (arity : R → ℕ) {V : Type}
    (r : (a : R) → (Fin (arity a) → V) → Prop) (S : Set V) :
    (relational arity r).IsClosed S := by
  intro F
  exact Empty.elim F

theorem relational_total {R : Type} [Finite R] (arity : R → ℕ) {V : Type}
    (r : (a : R) → (Fin (arity a) → V) → Prop) : (relational arity r).Total := by
  intro F
  exact Empty.elim F

theorem relational_closure {R : Type} [Finite R] (arity : R → ℕ) {V : Type}
    (r : (a : R) → (Fin (arity a) → V) → Prop) (S : Set V) :
    (relational arity r).closure S = S :=
  (relational arity r).closure_eq (relational_closed arity r S)

def unarySignature (F : Type) [Finite F] : Signature where
  Sorts := Unit
  Func := F
  Rel := Empty
  input _ := ()
  output _ := ()
  arity := Empty.elim
  argument R := Empty.elim R
  finiteSort := inferInstance
  finiteFunc := inferInstance
  finiteRel := inferInstance

def unary {F V : Type} [Finite F] (f : F → V → Set V)
    (hf : ∀ F x y z, y ∈ f F x → z ∈ f F x → y = z) :
    Structure (unarySignature F) V where
  sort _ := ()
  func := f
  functional := hf
  func_sorted _ _ _ _ := ⟨rfl, rfl⟩
  rel R := Empty.elim R
  rel_sorted R := Empty.elim R

theorem empty_irreducible {L : Signature} {V : Type} [IsEmpty V]
    (C : Structure L V) : C.Irreducible := by
  constructor
  intro d
  apply d.left_proper
  exact Set.eq_univ_of_forall (fun x => isEmptyElim x)

end CCO.UnarySupport.Boundaries
