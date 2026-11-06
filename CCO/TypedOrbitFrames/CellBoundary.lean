import CCO.UnaryFreshFrames.ClosureActions
import Mathlib.Logic.Equiv.Prod
import Mathlib.Logic.Equiv.Sum
import Mathlib.Order.Irreducible
import Mathlib.Tactic.FinCases

/-!
# Source11 C57: naming the non-MI cell quotient creates algebraicity

This is the actual infinite rows × columns × infinite-clones model,
with a finite typed unary signature. Real points project to their row,
column and cell; a cell projects to its row and column. Row and column
orphans have no outgoing nonidentity term. Their common cell is uniquely
determined by BOTH projections, is fixed by every full automorphism over
the two orphans, and is outside their actual unary closure.

The cell kernel is the proper nonidentity meet of two strictly larger
coordinate kernels, hence is not meet-irreducible. It is nevertheless
an equality-inclusive RAW square of an actual diversity relation.
This negative signature boundary assumes no homogeneity, old or hidden
SAP, semantic CCO, or finite approximation in place of the infinite model.
-/

namespace CCO.TypedOrbitFrames.CellBoundary

open CCO.UnaryFreshFrames

abbrev Real := (Nat × Nat) × Nat
abbrev Point := Real ⊕ (Nat ⊕ (Nat ⊕ (Nat × Nat)))

def real (r c n : Nat) : Point := .inl ((r,c),n)
def row (r : Nat) : Point := .inr (.inl r)
def column (c : Nat) : Point := .inr (.inr (.inl c))
def cell (r c : Nat) : Point := .inr (.inr (.inr (r,c)))

def sort : Point → Fin 4
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr (.inl _)) => 2
  | .inr (.inr (.inr _)) => 3

/-- Five actual primitive functions: real→row/column/cell and
cell→row/column. Off the input sort each function is the identity. -/
abbrev language : Language where
  Sorts := Fin 4
  Func := Fin 5
  Rel := PEmpty
  input F := if F < 3 then 0 else 3
  output F := if F = 0 ∨ F = 3 then 1 else if F = 1 ∨ F = 4 then 2 else 3
  arity := PEmpty.elim
  argument R := PEmpty.elim R

def operation (F : Fin 5) : Point → Point
  | .inl x =>
    if F = 0 then row x.1.1 else if F = 1 then column x.1.2
    else if F = 2 then cell x.1.1 x.1.2 else .inl x
  | .inr (.inl r) => row r
  | .inr (.inr (.inl c)) => column c
  | .inr (.inr (.inr p)) =>
    if F = 3 then row p.1 else if F = 4 then column p.2 else cell p.1 p.2

def model : Structure language Point where
  sort := sort
  func := operation
  func_sort := by
    intro F x hx
    fin_cases F <;>
      rcases x with ⟨⟨r,c⟩,n⟩ | (r | (c | ⟨r,c⟩)) <;>
      simp_all [language,sort,operation,row,column,cell]
  func_offsort := by
    intro F x hx
    fin_cases F <;>
      rcases x with ⟨⟨r,c⟩,n⟩ | (r | (c | ⟨r,c⟩)) <;>
      simp_all [language,sort,operation,row,column,cell]
  rel R := PEmpty.elim R
  rel_sort R := PEmpty.elim R

theorem actual_scope : Countable Point ∧ Finite language.Sorts ∧
    Finite language.Func ∧ Finite language.Rel :=
  ⟨inferInstance,inferInstance,inferInstance,inferInstance⟩

/-- Independent permutations of the three infinite old coordinates,
with their literal induced actions on row, column and cell quotients. -/
def coordinateEquiv (ρ κ ν : Equiv.Perm Nat) : Equiv.Perm Point :=
  Equiv.sumCongr (Equiv.prodCongr (Equiv.prodCongr ρ κ) ν)
    (Equiv.sumCongr ρ (Equiv.sumCongr κ (Equiv.prodCongr ρ κ)))

/-- These are constructed automorphisms of the FULL actual finite
unary signature, rather than motions postulated by a model provider. -/
def coordinateAut (ρ κ ν : Equiv.Perm Nat) : model.Aut := by
  refine ⟨coordinateEquiv ρ κ ν,?_,?_,?_⟩
  · intro x
    rcases x with ⟨⟨r,c⟩,n⟩ | (r | (c | ⟨r,c⟩)) <;> rfl
  · intro F x
    fin_cases F <;>
      rcases x with ⟨⟨r,c⟩,n⟩ | (r | (c | ⟨r,c⟩)) <;> rfl
  · intro R
    exact PEmpty.elim R

@[simp] theorem coordinateAut_real (ρ κ ν : Equiv.Perm Nat) (r c n : Nat) :
    coordinateAut ρ κ ν • real r c n = real (ρ r) (κ c) (ν n) := rfl

@[simp] theorem coordinateAut_row (ρ κ ν : Equiv.Perm Nat) (r : Nat) :
    coordinateAut ρ κ ν • row r = row (ρ r) := rfl

@[simp] theorem coordinateAut_column (ρ κ ν : Equiv.Perm Nat) (c : Nat) :
    coordinateAut ρ κ ν • column c = column (κ c) := rfl

@[simp] theorem coordinateAut_cell (ρ κ ν : Equiv.Perm Nat) (r c : Nat) :
    coordinateAut ρ κ ν • cell r c = cell (ρ r) (κ c) := rfl

/-- Actual real-sort transitivity is witnessed by three independent
coordinate swaps in the infinite source. -/
theorem real_sort_transitive (r c n r' c' n' : Nat) :
    ∃ g : model.Aut, g • real r c n = real r' c' n' := by
  refine ⟨coordinateAut (Equiv.swap r r') (Equiv.swap c c')
    (Equiv.swap n n'),?_⟩
  simp

/-- Each actual cell contains infinitely many distinct old real clones. -/
theorem real_cell_fibre_infinite (r c : Nat) :
    {x : Real | x.1 = (r,c)}.Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : Nat => ((r,c),n))
  · intro n m h
    exact congrArg Prod.snd h
  · intro n
    rfl

theorem actual_named_projections (r c n : Nat) :
    operation 0 (real r c n) = row r ∧
    operation 1 (real r c n) = column c ∧
    operation 2 (real r c n) = cell r c ∧
    operation 3 (cell r c) = row r ∧
    operation 4 (cell r c) = column c :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

def orphanBase (r c : Nat) : Set Point := {row r,column c}

theorem orphan_base_finite (r c : Nat) : (orphanBase r c).Finite :=
  (Set.finite_singleton (column c)).insert (row r)

/-- The TWO original quotient orphans already form a unary-closed base;
no real representative or additional cell is inserted by unary closure. -/
theorem orphan_base_closed (r c : Nat) : model.Closed (orphanBase r c) := by
  intro F x hx
  change operation F x ∈ orphanBase r c
  rcases hx with rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem orphan_base_closure (r c : Nat) :
    model.closure (orphanBase r c) = orphanBase r c :=
  model.closure_eq (orphan_base_closed r c)

theorem cell_outside_unary_closure (r c : Nat) :
    cell r c ∉ model.closure (orphanBase r c) := by
  rw [orphan_base_closure]
  simp [orphanBase,row,column,cell]

/-- The cell is specified by one row and one column TOGETHER.
This is uniqueness on the actual infinite hidden carrier. -/
theorem unique_cell (r c : Nat) :
    ∃! x : Point, sort x = 3 ∧
      operation 3 x = row r ∧ operation 4 x = column c := by
  refine ⟨cell r c,⟨rfl,rfl,rfl⟩,?_⟩
  intro x hx
  rcases x with ⟨⟨r',c'⟩,n⟩ | (r' | (c' | ⟨r',c'⟩))
  all_goals simp [sort,operation,row,column,cell] at hx ⊢
  exact hx

/-- EVERY full automorphism of the actual named structure fixing both
orphans fixes their unique cell; no restricted action is substituted. -/
theorem cell_fixed_by_full_aut (r c : Nat) (g : model.Aut)
    (hRow : g • row r = row r) (hColumn : g • column c = column c) :
    g • cell r c = cell r c := by
  apply (unique_cell r c).unique
  · refine ⟨model.aut_sort g (cell r c),?_,?_⟩
    · have h := model.aut_func g 3 (cell r c)
      change g • row r = operation 3 (g • cell r c) at h
      exact h.symm.trans hRow
    · have h := model.aut_func g 4 (cell r c)
      change g • column c = operation 4 (g • cell r c) at h
      exact h.symm.trans hColumn
  · exact ⟨rfl,rfl,rfl⟩

/-- Actual multi-parameter definability, and therefore algebraicity,
strictly outside the named unary closure. -/
theorem cell_algebraic_outside_unary_closure (r c : Nat) :
    cell r c ∈ Dcl model.Aut (orphanBase r c) ∧
    cell r c ∈ Acl model.Aut (orphanBase r c) ∧
    cell r c ∉ model.closure (orphanBase r c) := by
  have hDef : cell r c ∈ Dcl model.Aut (orphanBase r c) := by
    intro g
    exact cell_fixed_by_full_aut r c g.val
      (g.property (row r) (Or.inl rfl))
      (g.property (column c) (Or.inr rfl))
  exact ⟨hDef,dcl_subset_acl model.Aut (orphanBase r c) hDef,
    cell_outside_unary_closure r c⟩

/-- A SINGLE row orphan has infinitely many cells above it. In
particular its stabiliser cannot equivariantly select one cell. -/
theorem cell_orbit_over_one_row_infinite (r c : Nat) :
    (orbitOver model.Aut {row r} (cell r c)).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : Nat => cell r n)
  · intro n m h
    simpa [cell] using h
  · intro n
    apply (mem_orbitOver_iff model.Aut).mpr
    refine ⟨coordinateAut (Equiv.refl Nat) (Equiv.swap c n)
      (Equiv.refl Nat),?_,?_⟩
    · intro a ha
      have h : a = row r := ha
      subst a
      rfl
    · simp

/-- Symmetrically a SINGLE column orphan has infinitely many cells
above it. Algebraicity of the cross-cell uses BOTH orphan parameters. -/
theorem cell_orbit_over_one_column_infinite (r c : Nat) :
    (orbitOver model.Aut {column c} (cell r c)).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f := fun n : Nat => cell n c)
  · intro n m h
    simpa [cell] using h
  · intro n
    apply (mem_orbitOver_iff model.Aut).mpr
    refine ⟨coordinateAut (Equiv.swap r n) (Equiv.refl Nat)
      (Equiv.refl Nat),?_,?_⟩
    · intro a ha
      have h : a = column c := ha
      subst a
      rfl
    · simp

def rowKernel : Setoid Real := Setoid.ker (fun x : Real => x.1.1)
def columnKernel : Setoid Real := Setoid.ker (fun x : Real => x.1.2)
def cellKernel : Setoid Real := Setoid.ker (fun x : Real => x.1)

theorem actual_projection_kernels (x y : Real) :
    (operation 0 (.inl x) = operation 0 (.inl y) ↔ rowKernel x y) ∧
    (operation 1 (.inl x) = operation 1 (.inl y) ↔ columnKernel x y) ∧
    (operation 2 (.inl x) = operation 2 (.inl y) ↔ cellKernel x y) := by
  rcases x with ⟨⟨r,c⟩,n⟩
  rcases y with ⟨⟨r',c'⟩,n'⟩
  change (row r = row r' ↔ r = r') ∧
    (column c = column c' ↔ c = c') ∧
    (cell r c = cell r' c' ↔ (r,c) = (r',c'))
  simp [row,column,cell]

/-- Every actual full automorphism preserves every named projection
kernel; this quantifies over the full structure group, not just the
explicit independent coordinate motions constructed above. -/
theorem full_aut_projection_kernel (g : model.Aut) (F : Fin 5) (x y : Point) :
    operation F (g • x) = operation F (g • y) ↔
      operation F x = operation F y := by
  change model.func F (g • x) = model.func F (g • y) ↔
    model.func F x = model.func F y
  rw [← model.aut_func g F x, ← model.aut_func g F y]
  exact g.val.injective.eq_iff

/-- The actual real row, column and cell kernels are invariant under
EVERY full automorphism's original real restriction. The right sides
are the literal old coordinate equivalences used in the meet witness. -/
theorem full_aut_actual_kernel_readings (g : model.Aut) (x y : Real) :
    (operation 0 (g • (.inl x : Point)) = operation 0 (g • .inl y) ↔
      rowKernel x y) ∧
    (operation 1 (g • (.inl x : Point)) = operation 1 (g • .inl y) ↔
      columnKernel x y) ∧
    (operation 2 (g • (.inl x : Point)) = operation 2 (g • .inl y) ↔
      cellKernel x y) :=
  ⟨(full_aut_projection_kernel g 0 _ _).trans (actual_projection_kernels x y).1,
    (full_aut_projection_kernel g 1 _ _).trans (actual_projection_kernels x y).2.1,
    (full_aut_projection_kernel g 2 _ _).trans (actual_projection_kernels x y).2.2⟩

/-- The additional cell quotient is the literal meet of its two
original coordinate kernels, not another MI direction. -/
theorem cell_kernel_eq_meet : cellKernel = rowKernel ⊓ columnKernel := by
  apply Setoid.ext
  intro x y
  change x.1 = y.1 ↔ x.1.1 = y.1.1 ∧ x.1.2 = y.1.2
  exact Prod.ext_iff

theorem row_kernel_not_le_cell : ¬ rowKernel ≤ cellKernel := by
  intro h
  have he : ((0,0) : Nat × Nat) = (0,1) :=
    h (show rowKernel ((0,0),0) ((0,1),0) from rfl)
  exact Nat.zero_ne_one (congrArg Prod.snd he)

theorem column_kernel_not_le_cell : ¬ columnKernel ≤ cellKernel := by
  intro h
  have he : ((0,0) : Nat × Nat) = (1,0) :=
    h (show columnKernel ((0,0),0) ((1,0),0) from rfl)
  exact Nat.zero_ne_one (congrArg Prod.fst he)

theorem cell_kernel_not_meet_irreducible : ¬ InfIrred cellKernel := by
  intro hMI
  rcases hMI.2 cell_kernel_eq_meet.symm with hRow | hColumn
  · exact row_kernel_not_le_cell (le_of_eq hRow)
  · exact column_kernel_not_le_cell (le_of_eq hColumn)

theorem cell_kernel_nonidentity : cellKernel ≠ ⊥ := by
  intro hBot
  have h : cellKernel ((0,0),0) ((0,0),1) := rfl
  rw [hBot] at h
  have he : ((0,0),0) = (((0,0),1) : Real) := h
  exact Nat.zero_ne_one (congrArg Prod.snd he)

theorem cell_kernel_proper : cellKernel ≠ ⊤ := by
  intro hTop
  apply row_kernel_not_le_cell
  rw [hTop]
  exact le_top

/-- The real same-cell diversity atom: the clone coordinates differ. -/
def sameCellDiversity (x y : Real) : Prop := x.1 = y.1 ∧ x.2 ≠ y.2

/-- CELL is nevertheless an actual equality-inclusive RAW exact
two-step relation. Infinite clones supply an intermediate point distinct
from BOTH endpoints, including when those endpoints are equal. -/
theorem cell_kernel_raw_square (x y : Real) :
    cellKernel x y ↔
      ∃ z : Real, sameCellDiversity x z ∧ sameCellDiversity z y := by
  constructor
  · intro hxy
    let z : Real := (x.1, max x.2 y.2 + 1)
    have hX : x.2 < max x.2 y.2 + 1 :=
      Nat.lt_succ_of_le (Nat.le_max_left _ _)
    have hY : y.2 < max x.2 y.2 + 1 :=
      Nat.lt_succ_of_le (Nat.le_max_right _ _)
    exact ⟨z,⟨rfl,ne_of_lt hX⟩,⟨hxy,ne_of_gt hY⟩⟩
  · rintro ⟨z,hxz,hzy⟩
    exact hxz.1.trans hzy.1

end CCO.TypedOrbitFrames.CellBoundary
