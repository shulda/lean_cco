import CCO.ResetOrder.Hierarchy.Quotients
import CCO.ResetOrder.Hierarchy.Charts
import Mathlib.Data.Fintype.Prod

/-! C52's actual distributive equivalence lattice, quotient grid and two
transition charts. Fibre synchronization does not imply global monotonicity. -/
namespace CCO.ResetOrder.Hierarchy.GridBoundary
structure Level where
  value : Fin 6
deriving DecidableEq

instance levelFintype : Fintype Level :=
  Fintype.ofEquiv (Fin 6) ⟨Level.mk, Level.value, fun _ => rfl, fun _ => rfl⟩

def levelLE (a b : Level) : Prop := a.value ≤ b.value ∧ ¬ (a.value = 3 ∧ b.value = 4)
def cross (a b : Level) : Prop :=
  (a.value = 3 ∧ b.value = 4) ∨ (a.value = 4 ∧ b.value = 3)
instance levelLEDecidable : DecidableRel levelLE := by intro a b; unfold levelLE; infer_instance
instance crossDecidable : DecidableRel cross := by intro a b; unfold cross; infer_instance

def levelInf (a b : Level) : Level := if cross a b then ⟨2⟩ else ⟨min a.value b.value⟩
def levelSup (a b : Level) : Level := if cross a b then ⟨5⟩ else ⟨max a.value b.value⟩

instance levelDistribLattice : DistribLattice Level where
  le := levelLE
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  inf := levelInf
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide
  sup := levelSup
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  le_sup_inf := by decide

instance levelDecidableLE : DecidableLE Level := levelLEDecidable
instance levelDecidableLT : DecidableLT Level := by
  intro a b
  change Decidable (levelLE a b ∧ ¬ levelLE b a)
  infer_instance

instance levelTop : OrderTop Level where
  top := ⟨5⟩
  le_top := by decide

abbrev J : Level := ⟨1⟩
abbrev P : Level := ⟨2⟩
abbrev L : Level := ⟨3⟩
abbrev M : Level := ⟨4⟩
abbrev Original := Fin 2 × Fin 2 × Fin 2 × Fin 2
abbrev Grid := Fin 2 × Fin 2 × Fin 2

def equivalent (k : Level) (x y : Original) : Prop :=
  match k.value.val with
  | 0 => x = y
  | 1 => x.2 = y.2
  | 2 => x.2.2 = y.2.2
  | 3 => x.2.2.1 = y.2.2.1
  | 4 => x.2.2.2 = y.2.2.2
  | _ => True

instance equivalentDecidable (k : Level) : DecidableRel (equivalent k) := by
  intro x y
  unfold equivalent
  split <;> infer_instance

def relation (k : Level) : Setoid Original where
  r := equivalent k
  iseqv := ⟨(show ∀ k x, equivalent k x x from by decide) k,
    (show ∀ k {x y}, equivalent k x y → equivalent k y x from by decide) k,
    (show ∀ k {x y z}, equivalent k x y → equivalent k y z → equivalent k x z from by decide) k⟩

def geometry : EquivalenceLattice Level Original where
  relation := relation
  faithful := by
    intro i j h
    have hh : ∀ x y, equivalent i x y ↔ equivalent j x y := by
      intro x y
      exact Iff.of_eq (congrArg (fun q : Setoid Original => q.r x y) h)
    have sep : ∀ i j, (∀ x y, equivalent i x y ↔ equivalent j x y) → i = j := by decide
    exact sep i j hh
  inf_eq := by
    intro i j
    apply Setoid.ext
    intro x y
    exact (show ∀ i j x y, equivalent (i ⊓ j) x y ↔ equivalent i x y ∧ equivalent j x y
      from by decide) i j x y
  top_eq := by
    apply Setoid.ext
    intro x y
    trivial

theorem J_meetIrreducible : InfIrred J := by unfold InfIrred IsMax; decide
theorem L_meetIrreducible : InfIrred L := by unfold InfIrred IsMax; decide
theorem M_meetIrreducible : InfIrred M := by unfold InfIrred IsMax; decide
theorem J_parent : miParent J = P := by
  apply Eq.symm
  apply miParent_unique J_meetIrreducible
  rw [covBy_iff_lt_and_eq_or_eq]
  decide

theorem proper_nonidentity_MI : ∀ k : Level,
    (InfIrred k ∧ k.value ≠ 0) ↔ k = J ∨ k = L ∨ k = M := by
  unfold InfIrred IsMax
  decide

def swapLevel (k : Level) : Level := if k = L then M else if k = M then L else k
theorem swapLevel_involutive : ∀ k, swapLevel (swapLevel k) = k := by decide
theorem swapLevel_order : ∀ i j, swapLevel i ≤ swapLevel j ↔ i ≤ j := by decide

def swapOriginal (x : Original) : Original := (x.1,x.2.1,x.2.2.2,x.2.2.1)
theorem actual_cut_transport : ∀ k x y,
    equivalent (swapLevel k) (swapOriginal x) (swapOriginal y) ↔ equivalent k x y := by decide

def upperIntervalTransition : {k : Level // J < k} ≃ {k : Level // J < k} where
  toFun k := ⟨swapLevel k.val, (show ∀ k, J < k → J < swapLevel k from by decide) k.val k.property⟩
  invFun k := ⟨swapLevel k.val, (show ∀ k, J < k → J < swapLevel k from by decide) k.val k.property⟩
  left_inv k := Subtype.ext (swapLevel_involutive k.val)
  right_inv k := Subtype.ext (swapLevel_involutive k.val)

def quotientJ (x : Original) : Grid := x.2
theorem quotientJ_surjective : Function.Surjective quotientJ := fun x => ⟨(0,x), rfl⟩
theorem quotientJ_kernel (x y : Original) : quotientJ x = quotientJ y ↔ equivalent J x y := Iff.rfl

def upL (x : Grid) : Fin 2 := x.2.1
def upM (x : Grid) : Fin 2 := x.2.2
def parent (x : Grid) : Fin 2 × Fin 2 := x.2
def swap (x : Grid) : Grid := (x.1,x.2.2,x.2.1)
theorem swap_swap (x : Grid) : swap (swap x) = x := by cases x with | mk c ab => cases ab; rfl
def swapEquiv : Grid ≃ Grid := ⟨swap, swap, swap_swap, swap_swap⟩
theorem transition_upL (x : Grid) : upL (swap x) = upM x := rfl
theorem transition_upM (x : Grid) : upM (swap x) = upL x := rfl
theorem transition_parent (x y : Grid) : parent (swap x) = parent (swap y) ↔ parent x = parent y := by
  exact (show ∀ x y : Grid, parent (swap x) = parent (swap y) ↔ parent x = parent y from by decide) x y

def priorityLT (x y : Grid) : Prop :=
  upL x < upL y ∨ (upL x = upL y ∧ (upM x < upM y ∨ (upM x = upM y ∧ x.1 < y.1)))
instance priorityLTDecidable : DecidableRel priorityLT := by intro x y; unfold priorityLT; infer_instance

def priorityOrder : TotalOrder Grid where
  lt := priorityLT
  irrefl := by decide
  trans := by decide
  total := by decide

theorem fibre_comparison : ∀ x y : Grid, parent x = parent y → (priorityLT x y ↔ x.1 < y.1) := by decide
theorem synchronized_fibres : ∀ x y : Grid, parent x = parent y →
    (priorityLT (swap x) (swap y) ↔ priorityLT x y) := by decide

def copyTransition (i j : Bool) : Grid ≃ Grid := if i = j then Equiv.refl _ else swapEquiv

def paths : TransitionPaths Bool (fun _ => Grid) where
  Path _ _ := Unit
  identity _ := ()
  compose _ _ := ()
  inverse _ := ()
  map {i j} _ := copyTransition i j
  map_identity _ _ := by simp [copyTransition]
  map_compose := by
    intro i j k p q x
    cases i <;> cases j <;> cases k <;> simp [copyTransition, swapEquiv, swap_swap]
  map_inverse := by
    intro i j p x
    cases i <;> cases j <;> simp [copyTransition, swapEquiv, swap_swap]
  holonomy _ _ := by simp [copyTransition]

theorem actual_global_monotonicity_failure :
    priorityLT (0,0,1) (0,1,0) ∧ priorityLT (swap (0,1,0)) (swap (0,0,1)) ∧
      ¬ priorityLT (swap (0,0,1)) (swap (0,1,0)) := by decide
end CCO.ResetOrder.Hierarchy.GridBoundary
